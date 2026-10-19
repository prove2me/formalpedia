-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.coeff_pow_norm_le_choose_weighted
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:52:40.229299+00:00
-- url     : https://prove2.me/submissions/531aed20-10be-4fb2-b230-d5865b8d7f9d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_pow_norm_le_choose_weighted_succ

open scoped BigOperators

theorem solution
    (τ : PowerSeries ℂ) (m n : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hτc : ∀ r, ‖PowerSeries.coeff r τ‖ ≤ C) :
    ‖PowerSeries.coeff n (τ ^ m)‖ ≤
      C ^ m *
        (if m = 0 then (if n = 0 then (1 : ℝ) else 0)
         else (Nat.choose (n + m - 1) n : ℝ)) := by
  induction m generalizing n with
  | zero =>
      by_cases hn : n = 0 <;> simp [hn]
  | succ m ih =>
      cases m with
      | zero =>
          simpa using hτc n
      | succ k =>
          apply OAI.PiExponent.LiteralAnalytic.coeff_pow_norm_le_choose_weighted_succ
            τ (Nat.succ k) n C hC hτc
          · omega
          · intro r
            exact ih r