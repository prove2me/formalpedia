-- Prove2me | solution 1 for GlobalTheory.FubiniStudyHessian.differentiableAt_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:05.066534+00:00
-- url     : https://prove2.me/submissions/3bbc503a-b9bf-4ea7-8b61-782de621aa7c

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
theorem _root_.solution (i : Fin n) (x : V n) : DifferentiableAt ℂ (fun w : V n => w i) x :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt
end GlobalTheory.FubiniStudyHessian
