-- Prove2me | solution 1 for GlobalTheory.one_add_two_mul_div_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:05.010181+00:00
-- url     : https://prove2.me/submissions/c44456d4-9e15-491f-b56e-0cf7bb24be7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution {d R : ℝ} (hd : 0 < d) (hR : d ≤ R) (n : ℕ) :
    (1 + 2 * R / d) ^ n ≤ (3 * R / d) ^ n := by
  have hR0 : 0 ≤ R := hd.le.trans hR
  refine pow_le_pow_left₀ (by positivity) ?_ n
  have h1 : 1 ≤ R / d := (one_le_div hd).2 hR
  have : 3 * R / d = R / d + 2 * R / d := by ring
  linarith
end GlobalTheory
