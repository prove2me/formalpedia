-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.coeff_pow_norm_le_choose_weighted_succ
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:56:52.731777+00:00
-- url     : https://prove2.me/submissions/561e5fed-06a1-4545-bee2-a478308996ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_mul_norm_le_choose_weighted_succ_general

open scoped BigOperators

theorem solution
    (τ : PowerSeries ℂ) (k n : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hτc : ∀ r, ‖PowerSeries.coeff r τ‖ ≤ C)
    (hk : 1 ≤ k)
    (hpow : ∀ r, ‖PowerSeries.coeff r (τ ^ k)‖ ≤
      C ^ k * (Nat.choose (r + k - 1) r : ℝ)) :
    ‖PowerSeries.coeff n (τ ^ (k + 1))‖ ≤
      C ^ (k + 1) * (Nat.choose (n + (k + 1) - 1) n : ℝ) := by
  rw [pow_succ]
  exact OAI.PiExponent.LiteralAnalytic.coeff_mul_norm_le_choose_weighted_succ_general
    (τ ^ k) τ k n C hC hpow hτc hk