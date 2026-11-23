-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.coef_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:42.848549+00:00
-- url     : https://prove2.me/submissions/dbb1904f-9a4d-4154-a1d2-9b856ae0cadd

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
theorem _root_.solution (a : ℕ → ℝ) (n : ℕ) : coef a n 0 = 1 := by
  induction n with
  | zero => simp [coef]
  | succ n ih => simp [coef, ih]
end GroundTheory.Automorphic.LineKernel
