-- Prove2me | solution 1 for ListHashFurstenberg.Main.claim_2_18
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:26:26.582552+00:00
-- url     : https://prove2.me/submissions/e72c1291-6854-4cdd-8894-74d863f1d5c8

import Mathlib

/-- Claim 2.18, p.18 of Kumar–Mon, STOC 2027 submission #1578. For `x ∈ (0, 1)`,
`⌈log(1/2) / log(1 - x)⌉ ≤ 2 / x`. -/
theorem solution (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (⌈Real.log (1 / 2) / Real.log (1 - x)⌉ : ℝ) ≤ 2 / x := by
  have h1 : 0 < 1 - x := by linarith
  have hl : Real.log (1 - x) < 0 := Real.log_neg h1 (by linarith)
  have hge : x ≤ -Real.log (1 - x) := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hr : Real.log (1 / 2) / Real.log (1 - x) = Real.log 2 / (-Real.log (1 - x)) := by
    rw [one_div, Real.log_inv, neg_div, div_neg]
  have hle : Real.log 2 / (-Real.log (1 - x)) ≤ Real.log 2 / x := by
    apply div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) hx0 hge
  have hc := Int.ceil_lt_add_one (Real.log (1 / 2) / Real.log (1 - x))
  rw [hr] at hc ⊢
  have : Real.log 2 / x + 1 ≤ 2 / x := by
    rw [← sub_nonneg]
    have : 2 / x - (Real.log 2 / x + 1) = (2 - Real.log 2 - x) / x := by field_simp; ring
    rw [this]
    apply div_nonneg _ hx0.le
    linarith
  linarith
