-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.weight_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:01.849507+00:00
-- url     : https://prove2.me/submissions/72ffaa06-539e-4351-b8e4-715b4d639153

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine

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
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (M : ℕ → ℝ) (p : ℕ) : 0 < weight M p := by
  unfold weight; split_ifs
  · exact one_pos
  · exact div_pos (by positivity) (lt_of_lt_of_le one_pos (le_max_left _ _))
end GroundTheory.Automorphic.LineKernel
