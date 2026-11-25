-- Prove2me | solution 1 for GlobalTheory.TwistLoc.basis_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:46:36.02096+00:00
-- url     : https://prove2.me/submissions/2f4dc81b-cf10-42cf-8855-7748fd14f60f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Theorems.Thm_GlobalTheory_TwistLoc_isComb_of_gs
import Theorems.Thm_GlobalTheory_SecPull_existsUnique_secPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
variable {X X' Y Y₁ Y₂ T Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K] {m : ℕ}
namespace GlobalTheory.TwistLoc
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    (θ : Y₁ ≅ Y₂) (π₁ : Y₁ ⟶ T) (π₂ : Y₂ ⟶ T) (hπ : θ.hom ≫ π₂ = π₁) (ψ₁ : K → (Y₁ ⟶ X)) (ψ₂ : K → (Y₂ ⟶ X'))
    (hψ : ∀ k, θ.hom ≫ ψ₂ k ≫ F = ψ₁ k) (ε : K → ℤ) (b₁ : Fin m → LB.Sec (LB.LinComb L ψ₁ ε))
    (b₂ : Fin m → LB.Sec (LB.LinComb L' ψ₂ ε)) (u : Fin m → Γ(T, ⊤)) (hu : ∀ i, IsUnit (u i))
    (hb : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L ψ₁ p →
      (r ≫ θ.hom) z ∈ LB.wchart L' ψ₂ q → gs r z (LB.wchart L ψ₁ p) ((b₁ i).f p) =
        gs (r ≫ π₁) z ⊤ (u i) * ((pw w ψ₂ ε (r ≫ θ.hom) z p q).val * gs (r ≫ θ.hom) z (LB.wchart L' ψ₂ q) ((b₂ i).f q)))
    (h₂ : ∀ s, ∃! c, IsComb π₂ b₂ s c) (s : LB.Sec (LB.LinComb L ψ₁ ε)) : ∃! c, IsComb π₁ b₁ s c := by
  have hc : ∀ k, ψ₂ k ≫ F = θ.inv ≫ ψ₁ k := fun k => by rw [← hψ, Iso.inv_hom_id_assoc]
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull X X' Y₁ Y₂ L L' F hL hL' w hw K ψ₂ ψ₁ ε θ.inv hc s
  obtain ⟨c, hc₂, uniq⟩ := h₂ a
  choose v hv using fun i => (hu i).exists_right_inv
  refine ⟨fun i => c i * v i, isComb_of_gs fun y p hy => ?_, fun c' hc' => ?_⟩
  · choose q hq using fun k => exists_chart hL' (ψ₂ k ((𝟙 Y₁ ≫ θ.hom) y))
    have mq : (𝟙 Y₁ ≫ θ.hom) y ∈ LB.wchart L' ψ₂ q := Set.mem_iInter.2 hq
    have e := ha _ (𝟙 Y₁ ≫ θ.hom) y p q (fun k => by
      show (θ.hom ≫ ψ₂ k ≫ F) y ∈ L.U (p k)
      rw [hψ]; exact Set.mem_iInter.1 hy k) hq
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at e
    refine e.trans ?_
    refine (congrArg (_ * ·) (hc₂.gs (𝟙 Y₁ ≫ θ.hom) y q mq)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Eq.trans ?_ (congrArg (_ * ·) (hb i _ (𝟙 Y₁) y p q hy mq)).symm
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← gs_mul _ y ⊤ trivial, _root_.mul_assoc (c i), mul_comm (v i), hv,
      _root_.mul_one, Category.assoc, hπ, mul_comm _ (gs _ y ⊤ (c i)), _root_.mul_assoc]
    rfl
  · have e : IsComb π₂ b₂ a (fun i => c' i * u i) := isComb_of_gs fun y q hy => by
      choose p hp using fun k => exists_chart hL (F (ψ₂ k y))
      have i₁ : θ.inv ≫ θ.hom = 𝟙 Y₂ := θ.inv_hom_id
      have mp : θ.inv y ∈ LB.wchart L ψ₁ p := Set.mem_iInter.2 fun k => by
        show (θ.inv ≫ ψ₁ k) y ∈ L.U (p k)
        rw [← hc]; exact hp k
      have e₁ := ha _ (𝟙 Y₂) y p q hp (Set.mem_iInter.1 hy)
      rw [Category.id_comp] at e₁
      have e₂ := hc'.gs θ.inv y p mp
      have e₃ := fun i => hb i _ θ.inv y p q mp (by rw [i₁]; exact hy)
      have hπ' : θ.inv ≫ π₁ = 𝟙 Y₂ ≫ π₂ := by rw [← hπ, Iso.inv_hom_id_assoc, Category.id_comp]
      rw [i₁] at e₃
      refine (Units.mul_right_inj (pw w ψ₂ ε (𝟙 Y₂) y p q)).1 (e₁.symm.trans (e₂.trans ?_))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => (congrArg (_ * ·) (e₃ i)).trans ?_
      rw [hπ', gs_mul _ y ⊤ trivial, ← _root_.mul_assoc, mul_left_comm]
      rfl
    have e' := uniq _ e
    funext i
    rw [← e', _root_.mul_assoc, hv, _root_.mul_one]
end GlobalTheory.TwistLoc
