-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.one_add_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:46.152156+00:00
-- url     : https://prove2.me/submissions/6be01290-8e0e-40a5-909b-8f22a60bf74b

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
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : (1 + x) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
  have h1 : 1 + x ≤ 2 * max 1 x := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 x) ^ m ≤ 1 + x ^ m := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg hx m]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hx m]
  calc (1 + x) ^ m ≤ (2 * max 1 x) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    _ = 2 ^ m * (max 1 x) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (1 + x ^ m) := mul_le_mul_of_nonneg_left h2 (by positivity)
end GroundTheory.Automorphic.LineKernel
