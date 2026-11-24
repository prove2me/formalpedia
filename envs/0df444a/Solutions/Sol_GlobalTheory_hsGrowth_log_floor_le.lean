-- Prove2me | solution 1 for GlobalTheory.hsGrowth_log_floor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:59:38.642571+00:00
-- url     : https://prove2.me/submissions/4f8933c5-4e22-4418-949e-0a9503f60f4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CountGrowthExponentialRadii

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y : ℝ} (hY : 0 < Y) :
    Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log 3 + |Real.log Y| := by
  have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  rcases lt_or_ge Y 1 with h | h
  · have : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr h
    simp only [this, mul_zero, zero_add, Nat.cast_one, Real.log_one]
    linarith [abs_nonneg (Real.log Y)]
  · have h1 : ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Y := by
      push_cast
      have := Nat.floor_le hY.le
      linarith
    calc Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (3 * Y) := Real.log_le_log (by positivity) h1
      _ = Real.log 3 + Real.log Y := Real.log_mul (by norm_num) hY.ne'
      _ ≤ Real.log 3 + |Real.log Y| := by linarith [le_abs_self (Real.log Y)]
end GlobalTheory
