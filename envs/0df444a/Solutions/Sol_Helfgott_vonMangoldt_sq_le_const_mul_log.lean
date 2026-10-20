-- Prove2me | solution 1 for Helfgott.vonMangoldt_sq_le_const_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T19:03:13.572644+00:00
-- url     : https://prove2.me/submissions/ff08cb5a-5c6c-4ddb-a253-9f0e8dbda07f

import Mathlib

open ArithmeticFunction Chebyshev

private theorem aux_sq (X : ℕ) (hX : 2 ≤ X) :
    ∑ n ∈ Finset.Icc 0 X, (ArithmeticFunction.vonMangoldt n) ^ 2 ≤
      Real.log X * ψ X := by
  have hXr : (1:ℝ) ≤ (X:ℝ) := by norm_cast; omega
  have hψ : ψ X = ∑ n ∈ Finset.Icc 0 X, ArithmeticFunction.vonMangoldt n := by
    rw [psi_eq_sum_Icc, Nat.floor_natCast]
  rw [hψ]
  calc
    ∑ n ∈ Finset.Icc 0 X, (ArithmeticFunction.vonMangoldt n) ^ 2
      = ∑ n ∈ Finset.Icc 0 X, ArithmeticFunction.vonMangoldt n *
          ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ ≤ ∑ n ∈ Finset.Icc 0 X, ArithmeticFunction.vonMangoldt n * Real.log ↑X := by
        apply Finset.sum_le_sum
        intro n hn
        refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
        by_cases hn1 : n ≤ 1
        · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
          · simp only [ArithmeticFunction.vonMangoldt_apply]
            simp
            exact Real.log_nonneg hXr
          · rw [vonMangoldt_apply_one]
            exact Real.log_nonneg hXr
        · push Not at hn1
          have hn1' : (1:ℝ) < (n:ℝ) := by norm_num; omega
          calc ArithmeticFunction.vonMangoldt n ≤ Real.log (n:ℝ) := vonMangoldt_le_log
            _ ≤ Real.log (↑X : ℝ) := Real.log_le_log (lt_trans zero_lt_one hn1') (Nat.cast_le.mpr (Finset.mem_Icc.1 hn).2)
    _ = ∑ n ∈ Finset.Icc 0 X, Real.log ↑X * ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = Real.log ↑X * ∑ n ∈ Finset.Icc 0 X, ArithmeticFunction.vonMangoldt n := by
        rw [Finset.mul_sum]

theorem solution (X : ℕ) (hX : 2 ≤ X) :
    ∑ n ∈ Finset.Icc 0 X, (ArithmeticFunction.vonMangoldt n) ^ 2 ≤
      (Real.log 4 + 4) * (X : ℝ) * Real.log X := by
  calc
    ∑ n ∈ Finset.Icc 0 X, (ArithmeticFunction.vonMangoldt n) ^ 2
      ≤ Real.log X * ψ X := aux_sq X hX
    _ ≤ Real.log X * ((Real.log 4 + 4) * X) :=
        mul_le_mul_of_nonneg_left (psi_le_const_mul_self (by positivity))
          (Real.log_nonneg (by norm_cast; omega))
    _ = (Real.log 4 + 4) * (X : ℝ) * Real.log X := by ring
