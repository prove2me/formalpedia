-- Prove2me | solution 1 for GlobalTheory.abs_factorial_mul_eval_sub_top_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:22:45.574906+00:00
-- url     : https://prove2.me/submissions/ce7ffbba-9f72-4b4b-b424-635818fcb5c4

import Mathlib

open Polynomial Finset

theorem solution (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ d) :
    ∃ C : ℕ, ∀ m : ℕ,
      |(d.factorial : ℚ) * p.eval (m : ℚ) - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d|
        ≤ C * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
  let S : ℚ := ∑ i ∈ range d, |p.coeff i|
  obtain ⟨C, hC⟩ := exists_nat_ge ((d.factorial : ℚ) * S)
  refine ⟨C, fun m => ?_⟩
  have hsum :
      p.eval (m : ℚ) - p.coeff d * (m : ℚ) ^ d =
        ∑ i ∈ range d, p.coeff i * (m : ℚ) ^ i := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), sum_range_succ]
    abel
  have hrewrite :
      |(d.factorial : ℚ) * p.eval (m : ℚ) - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d|
        = (d.factorial : ℚ) * |p.eval (m : ℚ) - p.coeff d * (m : ℚ) ^ d| := by
    rw [mul_assoc (d.factorial : ℚ) (p.coeff d), ← mul_sub, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hrewrite, hsum]
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg _
  have hm1 : (1 : ℚ) ≤ (m : ℚ) + 1 := le_add_of_nonneg_left hm0
  have hterm : ∀ i ∈ range d,
      |p.coeff i * (m : ℚ) ^ i| ≤ |p.coeff i| * ((m : ℚ) + 1) ^ (d - 1) := by
    intro i hi
    have hi' : i ≤ d - 1 := Nat.le_pred_of_lt (mem_range.mp hi)
    rw [abs_mul, abs_pow, abs_of_nonneg hm0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact le_trans (pow_le_pow_left₀ hm0 (le_add_of_nonneg_right zero_le_one) i)
      (pow_le_pow_right₀ hm1 hi')
  have hbound :
      |∑ i ∈ range d, p.coeff i * (m : ℚ) ^ i|
        ≤ S * ((m : ℚ) + 1) ^ (d - 1) := by
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    refine le_trans (sum_le_sum hterm) ?_
    rw [← sum_mul]
  have hpow : (0 : ℚ) ≤ ((m : ℚ) + 1) ^ (d - 1) :=
    pow_nonneg (le_trans zero_le_one hm1) _
  refine le_trans (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)) ?_
  rw [← mul_assoc, ← mul_assoc (C : ℚ)]
  refine mul_le_mul_of_nonneg_right ?_ hpow
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [S]
  · have hCd : (C : ℚ) ≤ (C : ℚ) * d := by
      have : (1 : ℚ) ≤ d := Nat.one_le_cast.mpr hd
      simpa using mul_le_mul_of_nonneg_left this (Nat.cast_nonneg C)
    exact le_trans hC hCd
