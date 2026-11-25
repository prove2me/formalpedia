-- Prove2me | solution 1 for GlobalTheory.ExpGTrans.secLin_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:06:55.797564+00:00
-- url     : https://prove2.me/submissions/c8bd022b-e71b-443f-8d52-4264c74bf1a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsGTransport
import Theorems.Thm_GlobalTheory_ExpGTrans_secLin_val
import Theorems.Thm_GlobalTheory_FieldBaseChange_secLin_iff_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ExpGTrans
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans
variable {X X' Y Y' Y₁ Y₁' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.ExpGTrans
theorem _root_.solution (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F))
    (φ₁ : K → (Y₁ ⟶ X)) (φ₁' : K → (Y₁' ⟶ X')) (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ)
    (h : Y₁ ⟶ Y) (h' : Y₁' ⟶ Y') (Θ : Y₁' ⟶ Y₁) (Φ : Y' ⟶ Y)
    (hφ : ∀ κ, φ₁ κ = h ≫ φ κ) (hφ' : ∀ κ, φ₁' κ = h' ≫ φ' κ) (hc : ∀ κ, φ' κ ≫ F = Φ ≫ φ κ)
    (hsq : Θ ≫ h = h' ≫ Φ) {n : ℕ} (c : Fin n → Γ(Y₁, ⊤)) (c' : Fin n → Γ(Y₁', ⊤))
    (hcc : ∀ i y, gs (𝟙 Y₁' ≫ Θ) y ⊤ (c i) = gs (𝟙 Y₁') y ⊤ (c' i))
    (s₁ : LB.Sec (LB.LinComb L φ₁ ε)) (s₁' : LB.Sec (LB.LinComb L' φ₁' ε))
    (s : Fin n → LB.Sec (LB.LinComb L φ ε)) (s' : Fin n → LB.Sec (LB.LinComb L' φ' ε))
    (H₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ₁' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ₁' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart L φ₁ p) (s₁.f p) =
        (∏ κ, gw w (r ≫ φ₁' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ₁' q) (s₁'.f q))
    (H : ∀ (i : Fin n) (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ Φ) z (LB.wchart L φ p) ((s i).f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) ((s' i).f q))
    (hS : GeneratorPullback.SecLin L φ₁ ε s₁ φ ε s h c) : GeneratorPullback.SecLin L' φ₁' ε s₁' φ' ε s' h' c' := by
  rw [GlobalTheory.FieldBaseChange.secLin_iff_val hL']
  intro y J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good L hL y (Empty.elim : Empty → (Y₁' ⟶ X)) Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have key := secLin_val hS Θ y hJ
  obtain ⟨p, hp⟩ : ∃ p : K → L.ι, p = fun κ => J (Θ ≫ φ₁ κ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : K → L'.ι, q = fun κ => J' (𝟙 Y₁' ≫ φ₁' κ) := ⟨_, rfl⟩
  have eJ : ∀ ψ ψ' : Y₁' ⟶ X, ψ = ψ' → ψ' y ∈ L.U (J ψ) := fun ψ ψ' e => e ▸ hJ ψ
  have eJ' : ∀ ψ ψ' : Y₁' ⟶ X', ψ = ψ' → ψ' y ∈ L'.U (J' ψ) := fun ψ ψ' e => e ▸ hJ' ψ
  have mp : ∀ κ, F ((φ₁' κ) ((𝟙 Y₁' : Y₁' ⟶ Y₁') y)) ∈ L.U (p κ) := fun κ => by
    rw [hp]
    exact eJ _ (𝟙 Y₁' ≫ φ₁' κ ≫ F)
      (by simp only [Category.id_comp, hφ, hφ', Category.assoc, reassoc_of% hsq, hc])
  have mq : ∀ κ, (φ₁' κ) ((𝟙 Y₁' : Y₁' ⟶ Y₁') y) ∈ L'.U (q κ) := fun κ => by
    rw [hq]
    exact hJ' _
  have mp' : ∀ κ, F ((φ' κ) (h' y)) ∈ L.U (p κ) := fun κ => by
    rw [hp]
    exact eJ _ (h' ≫ φ' κ ≫ F) (by simp only [hφ, reassoc_of% hsq, hc])
  have mq' : ∀ κ, (φ' κ) (h' y) ∈ L'.U (q κ) := fun κ => by
    rw [hq]
    exact eJ' _ (h' ≫ φ' κ) (by simp only [Category.id_comp, hφ'])
  have e1 := H₁ Y₁' (𝟙 Y₁') y p q mp mq
  have e2 := fun i => H i Y₁' h' y p q mp' mq'
  have k1 : sval s₁ Θ y J = gs (𝟙 Y₁' ≫ Θ) y (L.wchart φ₁ p) (s₁.f p) := by
    rw [Category.id_comp]
    exact sval_of s₁ Θ y J p (fun κ => by simp only [hp])
  have k2 : ∀ i, sval (s i) (Θ ≫ h) y J = gs (h' ≫ Φ) y (L.wchart φ p) ((s i).f p) := fun i => by
    rw [← hsq]
    exact sval_of (s i) (Θ ≫ h) y J p (fun κ => by simp only [hp, hφ, Category.assoc])
  have hA : sval s₁' (𝟙 Y₁') y J' = gs (𝟙 Y₁') y (L'.wchart φ₁' q) (s₁'.f q) :=
    sval_of s₁' (𝟙 Y₁') y J' q (fun κ => by simp only [hq])
  have hB : ∀ i, sval (s' i) (𝟙 Y₁' ≫ h') y J' = gs h' y (L'.wchart φ' q) ((s' i).f q) := fun i => by
    rw [sval_of (s' i) (𝟙 Y₁' ≫ h') y J' q (fun κ => by simp only [hq, hφ', Category.id_comp]),
      Category.id_comp]
  have hu : (∏ κ, gw w (𝟙 Y₁' ≫ φ₁' κ) y (p κ) (q κ) ^ ε κ) = ∏ κ, gw w (h' ≫ φ' κ) y (p κ) (q κ) ^ ε κ := by
    simp only [Category.id_comp, hφ']
  rw [k1, e1, hu] at key
  simp only [k2, e2] at key
  rw [hA]
  simp only [hB]
  refine (Units.mul_right_inj (∏ κ, gw w (h' ≫ φ' κ) y (p κ) (q κ) ^ ε κ)).mp (key.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hcc i y, Category.id_comp]
  ring
end GlobalTheory.ExpGTrans
