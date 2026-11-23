-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.exists_gl_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:03.742509+00:00
-- url     : https://prove2.me/submissions/d735054b-1080-4a88-a72e-27b659958c16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_BoundedBasis_det_of_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.BoundedBasis
theorem _root_.solution {v w : Fin r → Fin r → E} (hv : LinearIndependent E v)
    (hw : LinearIndependent E w) : ∃ γ : GL (Fin r) E, ∀ c : Fin r → E,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (c ᵥ* Matrix.of w) = c ᵥ* Matrix.of v := by
  have hw' : IsUnit (Matrix.of w)ᵀ.det := by
    rw [det_transpose]; exact (det_of_ne_zero hw).isUnit
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero ((Matrix.of v)ᵀ * ((Matrix.of w)ᵀ)⁻¹) ?_,
    fun c => ?_⟩
  · rw [det_mul, det_transpose]
    exact mul_ne_zero (det_of_ne_zero hv) (isUnit_nonsing_inv_det _ hw').ne_zero
  · change ((Matrix.of v)ᵀ * ((Matrix.of w)ᵀ)⁻¹) *ᵥ _ = _
    rw [← mulVec_transpose, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hw',
      Matrix.mul_one, mulVec_transpose]
end GlobalTheory.BoundedBasis
