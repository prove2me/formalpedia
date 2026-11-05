-- Prove2me | solution 1 for LL_Decomp1543a.block_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:31.110591+00:00
-- url     : https://prove2.me/submissions/f4cf00b3-7748-4499-8d9d-d76391de797e

import Mathlib

open Real Finset ArithmeticFunction

theorem solution (T : Finset ℕ) (z : ℕ → ℂ) :
    ‖∑ t ∈ T, (moebius t : ℂ) * z t‖ ≤
      √(∑ t ∈ T, |(moebius t : ℝ)|) * √(∑ t ∈ T, ‖z t‖ ^ 2) := by
  calc ‖∑ t ∈ T, (moebius t : ℂ) * z t‖ ≤ ∑ t ∈ T, ‖(moebius t : ℂ) * z t‖ := norm_sum_le _ _
    _ = ∑ t ∈ T, √|(moebius t : ℝ)| * (√|(moebius t : ℝ)| * ‖z t‖) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [norm_mul, ← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
        congr 1
        simp
    _ ≤ √(∑ t ∈ T, (√|(moebius t : ℝ)|) ^ 2) * √(∑ t ∈ T, (√|(moebius t : ℝ)| * ‖z t‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ √(∑ t ∈ T, |(moebius t : ℝ)|) * √(∑ t ∈ T, ‖z t‖ ^ 2) := by
        have h1 : ∑ t ∈ T, (√|(moebius t : ℝ)|) ^ 2 = ∑ t ∈ T, |(moebius t : ℝ)| :=
          Finset.sum_congr rfl fun t _ => Real.sq_sqrt (abs_nonneg _)
        rw [h1]
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
        refine Finset.sum_le_sum fun t _ => ?_
        rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
        have : |(moebius t : ℝ)| ≤ 1 := by
          have := ArithmeticFunction.abs_moebius_le_one (n := t)
          exact_mod_cast this
        have := sq_nonneg ‖z t‖
        nlinarith
