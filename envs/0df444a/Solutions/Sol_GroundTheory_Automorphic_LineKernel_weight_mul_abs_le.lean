-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.weight_mul_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:54.138648+00:00
-- url     : https://prove2.me/submissions/b72cf06e-384f-4ebb-8e56-79b7beb59050

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
theorem _root_.solution (M : ℕ → ℝ) (p : ℕ) :
    weight M p * |M p| ≤ (1 / 2) ^ p * max 1 |M 0| := by
  unfold weight; split_ifs with h
  · subst h; simp
  · have hm : 0 < max 1 |M p| := lt_of_lt_of_le one_pos (le_max_left _ _)
    calc (1 / 2) ^ p / max 1 |M p| * |M p| ≤ (1 / 2) ^ p := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hm]
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ ≤ (1 / 2) ^ p * max 1 |M 0| := le_mul_of_one_le_right (by positivity) (le_max_left _ _)
end GroundTheory.Automorphic.LineKernel
