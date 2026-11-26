-- Prove2me | solution 1 for GlobalTheory.factorial_mul_pow_mono
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:07:33.096208+00:00
-- url     : https://prove2.me/submissions/eec342fe-4561-4479-9f54-77f1ebef9411

import Mathlib

open scoped Nat

theorem solution {p N : ℕ} (hp : p ≤ N) {r : ℝ} (hr : 1 ≤ r) :
    ((p + 1)! : ℝ) * r ^ (2 * p + 1) ≤ (N + 1)! * r ^ (2 * N + 1) := by
  have hr0 : (0 : ℝ) ≤ r := le_trans (zero_le_one : (0 : ℝ) ≤ 1) hr
  have hfac : ((p + 1)! : ℝ) ≤ ((N + 1)! : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.succ_le_succ hp)
  have hpow : r ^ (2 * p + 1) ≤ r ^ (2 * N + 1) := by
    refine pow_le_pow_right₀ hr ?_
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 1
  exact mul_le_mul hfac hpow (pow_nonneg hr0 _) (by exact_mod_cast Nat.zero_le (N + 1)!)
