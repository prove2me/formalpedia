-- Prove2me | solution 1 for GlobalTheory.ClassMin.dotProduct_gram_pos_of_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:36.656257+00:00
-- url     : https://prove2.me/submissions/9f26e755-8d3d-4572-b5c5-89c609fc30b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_two_mul_eq_dotProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {ι : Type*} {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution [Fintype ι] (hQ : Q.PosDef) (e : Module.Basis ι ℤ X) {x : ι → ℚ}
    (hx : x ≠ 0) : 0 < (fun i => (x i : ℝ)) ⬝ᵥ (gram Q e *ᵥ fun i => (x i : ℝ)) := by
  obtain ⟨⟨D, hD⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
  choose y hy using h
  have hD0 : D ≠ 0 := nonZeroDivisors.ne_zero hD
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD0
  have hy' : ∀ i, (y i : ℚ) = D * x i := fun i => by simpa using hy i
  have hyx : (fun i => (e.repr (e.equivFun.symm y) i : ℝ)) = (D : ℝ) • fun i => (x i : ℝ) := by
    funext i
    have h1 : e.repr (e.equivFun.symm y) i = y i := congrFun (e.equivFun.apply_symm_apply y) i
    rw [h1, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast hy' i
  have hy0 : e.equivFun.symm y ≠ 0 := by
    intro h0
    have h1 : y = 0 := by simpa using (LinearEquiv.map_eq_zero_iff _).mp h0
    refine hx (funext fun i => ?_)
    have := hy' i
    rw [h1] at this
    simpa [hD0] using this.symm
  have h2 := two_mul_eq_dotProduct Q e (e.equivFun.symm y)
  rw [hyx, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h2
  have h3 := hQ _ hy0
  exact (pos_iff_pos_of_mul_pos (h2 ▸ mul_pos two_pos h3)).mp (mul_self_pos.mpr hD')
end GlobalTheory.ClassMin
