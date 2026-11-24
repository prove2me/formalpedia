-- Prove2me | solution 1 for GlobalTheory.ShiftedTheta.exp_neg_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:06:20.376998+00:00
-- url     : https://prove2.me/submissions/e6cbb923-31df-43b3-8c33-841d29ebd31d

import Mathlib

theorem solution {c : ℝ} (hc : 0 < c) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (-(c * (n : ℝ) ^ 2)) ≤ 2 / c ^ 2 * (1 / (n : ℝ) ^ 2) := by
  have hi : (1 : ℤ) ≤ n^2 := by have := sq_pos_of_ne_zero hn; omega
  have hn' : (1 : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast hi
  have h := Real.sum_le_exp_of_nonneg (show 0 ≤ c * (n:ℝ)^2 by positivity) 3
  simp [Finset.sum_range_succ, Nat.factorial] at h
  have hx : c^2 * (n:ℝ)^2 ≤ 2 * Real.exp (c * (n:ℝ)^2) := by
    nlinarith [mul_nonneg (sq_nonneg c) (mul_nonneg (sq_nonneg (n:ℝ)) (sub_nonneg.mpr hn'))]
  rw [Real.exp_neg, inv_eq_one_div, div_mul_div_comm, mul_one]
  exact (div_le_div_iff₀ (Real.exp_pos _) (mul_pos (sq_pos_of_pos hc) (by linarith))).mpr (by simpa using hx)
