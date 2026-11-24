-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FibSch.weight_le_of_one_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:30:02.84967+00:00
-- url     : https://prove2.me/submissions/6230d4e8-b680-4664-ab5a-95ff1f1fdaca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralUniformNearParameter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibSch
namespace GlobalTheory.CompanionTheory.FibSch
theorem _root_.solution {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ)
    (h : 1 + a ≤ M * (1 + b)) :
    (1 + b) ^ (-(n : ℝ)) ≤ M ^ n * (1 + a) ^ (-(n : ℝ)) := by
  have ha' : 0 < 1 + a := by linarith
  have hb' : 0 < 1 + b := by linarith
  rw [Real.rpow_neg ha'.le, Real.rpow_neg hb'.le, Real.rpow_natCast, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (pow_pos ha' n), inv_mul_le_iff₀ (pow_pos hb' n), ← mul_pow]
  rw [mul_comm (1 + b) M]
  exact pow_le_pow_left₀ ha'.le h n
end GlobalTheory.CompanionTheory.FibSch
