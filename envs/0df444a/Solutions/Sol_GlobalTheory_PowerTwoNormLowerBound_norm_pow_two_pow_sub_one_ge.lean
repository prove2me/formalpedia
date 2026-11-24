-- Prove2me | solution 1 for GlobalTheory.PowerTwoNormLowerBound.norm_pow_two_pow_sub_one_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:35.227088+00:00
-- url     : https://prove2.me/submissions/e2df9320-c8c9-4edd-9b6e-39ee2d007bad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerTwoNormLowerBound
namespace GlobalTheory.PowerTwoNormLowerBound
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < (1 / 2 : ℝ)) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    set w := z ^ (2 ^ k) with hw
    have hw1 : ‖w - 1‖ < 1 / 2 := h _
    have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
      have e : (2 : ℂ) = (w + 1) - (w - 1) := by ring
      have := norm_sub_le (w + 1) (w - 1)
      rw [← e] at this
      have n2 : ‖(2 : ℂ)‖ = 2 := by simp
      linarith
    have eq : z ^ (2 ^ (k + 1)) - 1 = (w - 1) * (w + 1) := by
      rw [hw, pow_succ, pow_mul]; ring
    rw [eq, norm_mul, pow_succ]
    have h0 : 0 ≤ ‖z - 1‖ := norm_nonneg _
    have h0' : 0 ≤ (3 / 2 : ℝ) ^ k := by positivity
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖w - 1‖ * ‖w + 1‖ := mul_le_mul ih h2 (by norm_num) (norm_nonneg _)
end GlobalTheory.PowerTwoNormLowerBound
