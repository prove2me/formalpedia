-- Prove2me | solution 1 for GlobalTheory.FubiniStudyHessian.cHess_log_one_add_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:50.352239+00:00
-- url     : https://prove2.me/submissions/ce3dce32-4597-4d99-a4eb-4ae37d1b547f

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianLogOneAddNormSq
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_differentiableAt_coord
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_wd_coord
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_differentiableAt_normSq
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_wd_normSq
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_wdb_log
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FubiniStudyHessian
open ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {n : ℕ}
namespace GlobalTheory.FubiniStudyHessian
theorem _root_.solution : ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v = Matrix.of (fun j l => (if j = l then 1 else 0) / (1 + (‖v‖ : ℂ) ^ 2) - (starRingEnd ℂ (v j) * v l) / (1 + (‖v‖ : ℂ) ^ 2) ^ 2) := by
  intro n v
  ext j l
  have hpos : (1 + ‖v‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hk : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-1 / (1 + ‖v‖ ^ 2) ^ 2) (‖v‖ ^ 2) :=
    ((hasDerivAt_id' (‖v‖ ^ 2)).const_add 1).inv hpos
  have hd : DifferentiableAt ℝ (fun w : V n => (1 + ‖w‖ ^ 2)⁻¹) v :=
    ((differentiableAt_normSq v).const_add 1).inv hpos
  simp only [cHess, Matrix.of_apply]
  rw [wdb_log, wd_mul (differentiableAt_ofReal hd) ((differentiableAt_coord l v).restrictScalars ℝ),
    wd_ofReal_comp (k := fun t : ℝ => (1 + t)⁻¹) (v := fun w : V n => ‖w‖ ^ 2)
      hk.differentiableAt (differentiableAt_normSq v), hk.deriv, wd_normSq, wd_coord]
  push_cast
  ring
end GlobalTheory.FubiniStudyHessian
