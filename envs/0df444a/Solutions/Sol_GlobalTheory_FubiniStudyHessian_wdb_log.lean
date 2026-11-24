-- Prove2me | solution 1 for GlobalTheory.FubiniStudyHessian.wdb_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:07:47.592901+00:00
-- url     : https://prove2.me/submissions/3a86825e-75cd-4a50-9029-26894868f79f

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianLogOneAddNormSq
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_differentiableAt_normSq
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_wdb_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_ofReal_comp


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
theorem _root_.solution (l : Fin n) :
    wdb n l (fun w : V n => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) =
      fun w => (((1 + ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * w l := by
  funext x
  have hpos : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hk : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + ‖x‖ ^ 2)) (‖x‖ ^ 2) :=
    ((hasDerivAt_id' (‖x‖ ^ 2)).const_add 1).log hpos
  rw [wdb_ofReal_comp (k := fun t : ℝ => Real.log (1 + t)) (v := fun w : V n => ‖w‖ ^ 2)
    hk.differentiableAt (differentiableAt_normSq x), hk.deriv, wdb_normSq, one_div]
end GlobalTheory.FubiniStudyHessian
