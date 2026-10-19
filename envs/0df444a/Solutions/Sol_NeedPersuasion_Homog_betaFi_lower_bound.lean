-- Prove2me | solution 1 for NeedPersuasion.Homog.betaFi_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T12:14:42.09293+00:00
-- url     : https://prove2.me/submissions/ed9307bd-9177-4ba3-b8ee-5cf1ef5472cb

import Mathlib
set_option autoImplicit false

theorem solution (lamL : ℝ) (m : ℕ) (h0 : 0 < lamL) (h1 : lamL ≤ 1) :
    1 - 1 / ((m : ℝ) + 1) ≤
      (∑ n ∈ Finset.range m, lamL ^ n) / (∑ n ∈ Finset.range (m + 1), lamL ^ n) := by
  have hpos : 0 < ∑ n ∈ Finset.range (m + 1), lamL ^ n :=
    Finset.sum_pos (fun n _ => pow_pos h0 n) ⟨0, by simp⟩
  have hbd : (m : ℝ) * lamL ^ m ≤ ∑ n ∈ Finset.range m, lamL ^ n := by
    calc (m : ℝ) * lamL ^ m = ∑ _n ∈ Finset.range m, lamL ^ m := by simp
      _ ≤ ∑ n ∈ Finset.range m, lamL ^ n :=
        Finset.sum_le_sum (fun n hn => pow_le_pow_of_le_one h0.le h1 (Finset.mem_range.1 hn).le)
  rw [Finset.sum_range_succ] at hpos ⊢
  rw [le_div_iff₀ hpos]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : 1 - 1 / ((m : ℝ) + 1) = (m : ℝ) / ((m : ℝ) + 1) := by field_simp; ring
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hm]
  nlinarith
