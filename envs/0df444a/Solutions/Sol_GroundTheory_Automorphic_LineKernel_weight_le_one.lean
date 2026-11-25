-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.weight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:52.568228+00:00
-- url     : https://prove2.me/submissions/efcd4969-5e65-44a5-baab-08bf75b070ff

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
theorem _root_.solution (M : ℕ → ℝ) (p : ℕ) : weight M p ≤ 1 := by
  unfold weight; split_ifs
  · exact le_rfl
  · rw [div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))]
    exact (pow_le_one₀ (by norm_num) (by norm_num)).trans (le_max_left _ _)
end GroundTheory.Automorphic.LineKernel
