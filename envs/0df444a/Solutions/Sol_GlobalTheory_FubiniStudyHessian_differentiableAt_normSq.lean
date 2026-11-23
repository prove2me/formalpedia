-- Prove2me | solution 1 for GlobalTheory.FubiniStudyHessian.differentiableAt_normSq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:05.588812+00:00
-- url     : https://prove2.me/submissions/86f71bd6-4569-43ba-aa29-c6caa44a58f6

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianLogOneAddNormSq

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
theorem _root_.solution (x : V n) : DifferentiableAt ℝ (fun w : V n => ‖w‖ ^ 2) x :=
  ((contDiff_norm_sq ℂ (n := 1)).differentiable one_ne_zero) x
end GlobalTheory.FubiniStudyHessian
