-- Prove2me | solution 1 for GlobalTheory.KS.Sym.dl_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:11.85299+00:00
-- url     : https://prove2.me/submissions/1cec3391-b536-4e69-b487-85506fa84936

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
import Theorems.Thm_GlobalTheory_KS_Sym_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_Sym_pbT_id
import Theorems.Thm_GlobalTheory_KS_Sym_pbT_val_inv
import Theorems.Thm_GlobalTheory_KS_Sym_tr_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
private lemma rsT_sub_moduli {O₀ : Z.Opens} (a b : Γ(Z, O₀)) (O : Z.Opens) :
    rsT (a - b) O = rsT a O - rsT b O := by
  unfold rsT
  split_ifs <;> simp
private lemma rsT_mul_moduli {O₀ : Z.Opens} (a b : Γ(Z, O₀)) (O : Z.Opens) :
    rsT (a * b) O = rsT a O * rsT b O := by
  unfold rsT
  split_ifs <;> simp
private lemma rsT_eq_resG_of_le_moduli {O₀ O : Z.Opens} (s : Γ(Z, O₀)) (h : O ≤ O₀) : rsT s O = resG Z h s := by
  unfold rsT
  rw [dif_pos h]
private lemma rsT_pbT_of_le_of_le_preimage (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) {O O' : Z.Opens} (h : O' ≤ O)
    (e : O ≤ f ⁻¹ᵁ O₀) : rsT (pbT f s O) O' = pbT f s O' := by
  unfold rsT pbT
  rw [dif_pos h, dif_pos e, dif_pos (h.trans e)]
  dsimp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
private lemma pbT_mul_moduli (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (a * b) O = pbT f a O * pbT f b O := by
  unfold pbT
  split_ifs <;> simp
private lemma rsT_sum_moduli {κ : Type} {O₀ : Z.Opens} (s : Finset κ) (F : κ → Γ(Z, O₀)) (O : Z.Opens) :
    rsT (∑ i ∈ s, F i) O = ∑ i ∈ s, rsT (F i) O := by
  unfold rsT
  split_ifs <;> simp
private lemma rsT_natCast_of_le {O₀ O : Z.Opens} (k : ℕ) (h : O ≤ O₀) : rsT (k : Γ(Z, O₀)) O = k := by
  rw [rsT_eq_resG_of_le_moduli _ h, map_natCast]
variable {K R : Type} [Field K] [CommRing R]
end GlobalTheory.KS.Sym
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
variable {K R : Type} [Field K] [CommRing R]
namespace GlobalTheory.KS.Sym
theorem _root_.solution {g : ℕ} {m : Y ⟶ X} {D : R → K}
    {q₂ : Z ⟶ Sp K} {s₂ : X₂ ⟶ Sp R} {m₂ : Z ⟶ X₂} {Q Q' Q₀ : X₂.Opens}
    {d₂ d₂' : ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Z, m₂ ⁻¹ᵁ O)} (hd₂ : LocDerK q₂ s₂ m₂ D Q d₂)
    (hd₂' : LocDerK q₂ s₂ m₂ D Q' d₂') {π : X₂ ⟶ X} {n p : Z ⟶ Y}
    (sq : m₂ ≫ π = n ≫ m) (l : Q₀ ≤ Q) (l' : Q₀ ≤ Q') {T : Y.Opens} (θ : Fin g → Γ(Y, T))
    (hT : m₂ ⁻¹ᵁ Q₀ ≤ p ⁻¹ᵁ T) {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    {w : Fin g → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hw : ∀ a, IsVF q₂ (w a))
    (hdiff : ∀ O, O ≤ Q₀ → ∀ f : Γ(X₂, O), d₂' O f - d₂ O f = ∑ a, pbT p (θ a) _ * w a _ (pbT m₂ f _))
    (ε : ℕ) (w₁ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ n ⁻¹ᵁ V → w a O (pbT n h O) = ε * pbT n (dd a V h) O)
    {L : LB X} {φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)} (hφ : IsDlog m L dd φ) (i j : L.ι) {O : Z.Opens}
    (hO : O ≤ m₂ ⁻¹ᵁ Q₀) (hi : O ≤ n ⁻¹ᵁ m ⁻¹ᵁ L.U i) (hj : O ≤ n ⁻¹ᵁ m ⁻¹ᵁ L.U j) :
    dl (n ≫ m) L (tr (𝟙 Z) m₂ π Q' d₂') i j O - dl (n ≫ m) L (tr (𝟙 Z) m₂ π Q d₂) i j O =
      ∑ a, pbT p (θ a) O * (ε * pbT n (φ a i j) O) := by
  have key : ∀ x, π.base (m₂.base x) = m.base (n.base x) := fun x => by
    simpa using congrArg (fun φ : Z ⟶ X => φ.base x) sq
  have hO3 : O ≤ m₂ ⁻¹ᵁ (π ⁻¹ᵁ (L.U i ⊓ L.U j) ⊓ Q₀) := fun x hx => by
    have a1 : m.base (n.base x) ∈ L.U i := hi hx
    have a2 : m.base (n.base x) ∈ L.U j := hj hx
    rw [← key] at a1 a2
    exact ⟨⟨a1, a2⟩, hO hx⟩
  have hN : m₂ ⁻¹ᵁ (π ⁻¹ᵁ (L.U i ⊓ L.U j) ⊓ Q₀) ≤ n ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) := fun x hx => by
    have b1 : π.base (m₂.base x) ∈ L.U i := hx.1.1
    have b2 : π.base (m₂.base x) ∈ L.U j := hx.1.2
    rw [key] at b1 b2
    exact ⟨b1, b2⟩
  have hNO : O ≤ n ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) := hO3.trans hN
  have hinv := pbT_val_inv (n ≫ m) (L.g i j) (O' := O) (fun x hx => hNO hx)
  unfold dl
  rw [tr_eq hd₂' (𝟙 Z) π _ (O₃ := π ⁻¹ᵁ (L.U i ⊓ L.U j) ⊓ Q₀) inf_le_left (inf_le_right.trans l') hO3,
    tr_eq hd₂ (𝟙 Z) π _ (O₃ := π ⁻¹ᵁ (L.U i ⊓ L.U j) ⊓ Q₀) inf_le_left (inf_le_right.trans l) hO3,
    pbT_id, pbT_id, ← sub_mul, ← rsT_sub_moduli, hdiff _ inf_le_right, rsT_sum_moduli, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [pbT_pbT m₂ π inf_le_left le_rfl, sq, ← pbT_pbT n m (O₀ := L.U i ⊓ L.U j) (O₁ := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun x hx => hx) hN,
    w₁ a _ _ _ hN, ← hφ a i j, pbT_mul_moduli]
  simp only [rsT_mul_moduli]
  rw [rsT_pbT_of_le_of_le_preimage p _ hO3 (fun x hx => hT hx.2), rsT_pbT_of_le_of_le_preimage n _ hO3 hN, rsT_pbT_of_le_of_le_preimage n _ hO3 hN,
    pbT_pbT n m (O₀ := L.U i ⊓ L.U j) (O₁ := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun x hx => hx) hNO, rsT_natCast_of_le _ hO3]
  linear_combination (pbT p (θ a) O * (ε * pbT n (φ a i j) O)) * hinv
end GlobalTheory.KS.Sym
