-- Prove2me | solution 1 for Hlawka1D.hlawka_1d
-- status  : ACCEPTED   (prove)
-- author  : @sorry_not_sorry
-- created : 2026-10-08T05:31:33.518504+00:00
-- url     : https://prove2.me/submissions/cf55d87e-25b5-4196-a18e-f3a6c3dcf4c8

import Mathlib

theorem solution : ∀ a b c : ℝ,
    |a + b| + |b + c| + |c + a| ≤ |a| + |b| + |c| + |a + b + c| := by
  intro a b c
  have h1 : |a + b| = (a + b) ∨ |a + b| = -(a + b) := by
    rcases le_or_gt 0 (a + b) with h | h
    · left; exact abs_of_nonneg h
    · right; exact abs_of_neg h
  have h2 : |b + c| = (b + c) ∨ |b + c| = -(b + c) := by
    rcases le_or_gt 0 (b + c) with h | h
    · left; exact abs_of_nonneg h
    · right; exact abs_of_neg h
  have h3 : |c + a| = (c + a) ∨ |c + a| = -(c + a) := by
    rcases le_or_gt 0 (c + a) with h | h
    · left; exact abs_of_nonneg h
    · right; exact abs_of_neg h
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rw [h1, h2, h3] <;>
    linarith [le_abs_self a, le_abs_self b, le_abs_self c, le_abs_self (a + b + c),
              neg_le_abs a, neg_le_abs b, neg_le_abs c, neg_le_abs (a + b + c),
              abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg (a + b + c)]
