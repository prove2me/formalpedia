-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.weighted_choose_term_le_three_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T09:10:40.508792+00:00
-- url     : https://prove2.me/submissions/377ab5c8-d8e2-4c1d-8eb1-c833628f2042

import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (n k : ℕ) (hk : k ≤ n) :
    n.choose k * 2 ^ k ≤ 3 ^ n := by
  have hbound : ∀ m : ℕ, ∀ j : ℕ, m.choose j * 2 ^ j ≤ 3 ^ m := by
    intro m
    induction m with
    | zero =>
        intro j
        cases j <;> simp
    | succ m ih =>
        intro j
        cases j with
        | zero =>
            simp only [Nat.choose_zero_right, pow_zero, mul_one]
            have hpow : 0 < (3 : ℕ) ^ (m + 1) := pow_pos (by norm_num) _
            omega
        | succ j =>
            rw [Nat.choose_succ_succ]
            have h₁ := ih (j + 1)
            have h₀ := ih j
            calc
              (m.choose j + m.choose (j + 1)) * 2 ^ (j + 1)
                  = m.choose (j + 1) * 2 ^ (j + 1) +
                      (m.choose j * 2 ^ j) * 2 := by
                        rw [pow_succ]
                        ring
              _ ≤ 3 ^ m + 3 ^ m * 2 :=
                  Nat.add_le_add h₁ (Nat.mul_le_mul_right 2 h₀)
              _ = 3 ^ (m + 1) := by
                  rw [pow_succ]
                  ring
  exact hbound n k