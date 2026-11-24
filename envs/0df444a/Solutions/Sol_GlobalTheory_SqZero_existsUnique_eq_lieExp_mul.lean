-- Prove2me | solution 1 for GlobalTheory.SqZero.existsUnique_eq_lieExp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:47.137021+00:00
-- url     : https://prove2.me/submissions/614798e4-b253-486d-83b8-46bae4a0308d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_kerEquiv_eq_iff
import Theorems.Thm_GlobalTheory_SqZero_eq_lieExp_kerEquiv
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
namespace GlobalTheory.SqZero
theorem _root_.solution (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥)
    {y y' : sp A ⟶ G}
    (h : spMap (Ideal.Quotient.mkₐ R J) ≫ y = spMap (Ideal.Quotient.mkₐ R J) ≫ y') :
    ∃! c : Fin n → J,
      y' = lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2) * y := by
  have hmem : y' * y⁻¹ ∈ redKer G J := by
    show y' * y⁻¹ ∈ (pointsMap G (Ideal.Quotient.mkₐ R J)).ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ptsMap_apply, ptsMap_apply, h, mul_inv_cancel]
  refine ⟨kerEquiv hv hJ (Additive.ofMul ⟨_, hmem⟩), ?_, ?_⟩
  · have := eq_lieExp_kerEquiv hv hJ ⟨_, hmem⟩
    dsimp only
    rw [← this]
    exact (inv_mul_cancel_right y' y).symm
  · intro c hc
    have : (y' * y⁻¹ : sp A ⟶ G) =
        lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2) := by
      rw [hc, mul_inv_cancel_right]
    exact ((kerEquiv_eq_iff hv hJ ⟨_, hmem⟩ c).2 this).symm
end GlobalTheory.SqZero
