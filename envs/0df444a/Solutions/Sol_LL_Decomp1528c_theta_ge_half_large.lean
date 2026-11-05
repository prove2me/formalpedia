-- Prove2me | solution 1 for LL_Decomp1528c.theta_ge_half_large
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:09.438477+00:00
-- url     : https://prove2.me/submissions/5b1c8e66-4998-46aa-a4b4-9558c867d6fc

import Mathlib

open Real Finset Chebyshev

theorem solution (n : ℕ) (hn : 10 ^ 4 ≤ n) : ((n : ℝ) + 1) / 2 ≤ θ n := by
  have hn' : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Chebyshev.theta_ge n
  set s := √(n : ℝ) with hs
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs100 : 100 ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; linarith
  have hlogn : Real.log n = 2 * Real.log s := by
    rw [hs, Real.log_sqrt (by linarith)]; ring
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have ht : Real.log s ≤ s / 128 + 3.8524 := by
    have := Real.log_le_sub_one_of_pos (show 0 < s / 128 by positivity)
    rw [Real.log_div (by positivity) (by norm_num),
      show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow] at this
    push_cast at this
    linarith
  have ht0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log n := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hprod : Real.log s * (4 * s + 2) ≤ (s / 128 + 3.8524) * (4 * s + 2) :=
    mul_le_mul_of_nonneg_right ht (by linarith)
  rw [hlogn] at h hlog1
  have : ((n : ℝ) + 1) / 2 ≤ n * Real.log 2 - Real.log ((n : ℝ) + 1) - 2 * s * (2 * Real.log s) := by
    rw [← hs2] at hlog1 ⊢
    nlinarith [sq_nonneg (s - 100)]
  linarith
