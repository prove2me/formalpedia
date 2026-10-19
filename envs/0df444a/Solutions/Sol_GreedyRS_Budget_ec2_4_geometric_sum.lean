-- Prove2me | solution 1 for GreedyRS.Budget.ec2_4_geometric_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:23:51.051251+00:00
-- url     : https://prove2.me/submissions/0049a104-6023-43d1-a1c9-e6ab9fa73df5

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≠ 0) (n0 : ℕ) :
    ∑' n : ℕ, Real.exp (-((n0 + n : ℕ) : ℝ) * x ^ 2 / 2) =
      Real.exp (-(n0 : ℝ) * x ^ 2 / 2) / (1 - Real.exp (-x ^ 2 / 2)) := by
  have hx2 : 0 < x ^ 2 := by positivity
  have hr0 : 0 ≤ Real.exp (-x ^ 2 / 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x ^ 2 / 2) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have key : ∀ n : ℕ, Real.exp (-((n0 + n : ℕ) : ℝ) * x ^ 2 / 2)
      = Real.exp (-(n0 : ℝ) * x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [key]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  ring
