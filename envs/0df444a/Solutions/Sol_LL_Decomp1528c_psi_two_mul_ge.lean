-- Prove2me | solution 1 for LL_Decomp1528c.psi_two_mul_ge
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:06.432066+00:00
-- url     : https://prove2.me/submissions/e15902bd-91ea-4f9d-9c6a-9e85c6e503fb

import Mathlib

open Real Finset Chebyshev

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * log 4 - log (2 * n + 1) ≤ ψ (2 * n) := by
  have h2 : (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
  have h := psi_ge (2 * n)
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  have : (n : ℝ) * log 4 = ((2 * n : ℕ) : ℝ) * log 2 := by
    rw [h4, Real.log_pow]; push_cast; ring
  rw [h2, this]
  push_cast at h ⊢
  exact h
