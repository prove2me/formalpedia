-- Prove2me | solution 1 for LevyStochCalc.Probability.summable_sqrt_pow_div_factorial
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:08:26.860392+00:00
-- url     : https://prove2.me/submissions/3de985e0-866c-41c1-b5b8-693177cb1a4c

import Mathlib.Analysis.SpecialFunctions.Exponential

theorem solution {x : ℝ} (hx : 0 ≤ x) :
    Summable fun r : ℕ => Real.sqrt (x ^ r / (r.factorial : ℝ)) := by
  have hsum : Summable fun r : ℕ => (((2 * x) ^ r / (r.factorial : ℝ) + (1 / 2 : ℝ) ^ r) / 2) :=
    ((Real.summable_pow_div_factorial (2 * x)).add summable_geometric_two).div_const 2
  refine Summable.of_nonneg_of_le (fun _ => Real.sqrt_nonneg _) (fun r => ?_) hsum
  have hu : 0 ≤ (2 * x) ^ r / (r.factorial : ℝ) := by positivity
  have hw : 0 ≤ (1 / 2 : ℝ) ^ r := by positivity
  have heq : x ^ r / (r.factorial : ℝ) = ((2 * x) ^ r / (r.factorial : ℝ)) * (1 / 2 : ℝ) ^ r := by
    rw [mul_pow, div_mul_eq_mul_div, mul_right_comm, ← mul_pow]
    norm_num
  rw [heq]
  have hsq : Real.sqrt (((2 * x) ^ r / (r.factorial : ℝ)) * (1 / 2 : ℝ) ^ r) ≤
      ((2 * x) ^ r / (r.factorial : ℝ) + (1 / 2 : ℝ) ^ r) / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((2 * x) ^ r / (r.factorial : ℝ) - (1 / 2 : ℝ) ^ r)]
  exact hsq
