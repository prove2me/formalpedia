-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.coef_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:30.544204+00:00
-- url     : https://prove2.me/submissions/bdb3fe71-ab0b-4ede-8ba7-7ece5e273b7a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (n p : ℕ) : 0 ≤ coef a n p := by
  induction n generalizing p with
  | zero => simp only [coef]; split_ifs <;> norm_num
  | succ n ih =>
    cases p with
    | zero => simp only [coef]; exact ih 0
    | succ p => simp only [coef]; exact add_nonneg (ih _) (div_nonneg (ih _) (ha n).le)
end GroundTheory.Automorphic.LineKernel
