-- Prove2me | solution 1 for GlobalTheory.T.continuousOn_complex_hessian_of_contDiffOn_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:17.634651+00:00
-- url     : https://prove2.me/submissions/bdab2463-3ebf-4e9c-9c3e-da76932e15cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwo
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwoStatement
import Theorems.Thm_GlobalTheory_continuousOn_cHess_of_contDiffOn_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l, ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by
  first | exact @GlobalTheory.continuousOn_cHess_of_contDiffOn_two | exact GlobalTheory.continuousOn_cHess_of_contDiffOn_two | (intros; apply GlobalTheory.continuousOn_cHess_of_contDiffOn_two <;> assumption)
end _root_.GlobalTheory.T
