-- Prove2me | solution 1 for Kyprianou.Ch02.poissonMeasureRealSecondMomentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:38:51.518881+00:00
-- url     : https://prove2.me/submissions/a7ece0fb-e523-4df1-8add-267b2a3c21e8

import Mathlib
import Definitions.Def_LevyStochCalc_Probability_PoissonMoments_F000
import Theorems.Thm_LevyStochCalc_Probability_integral_mul_eval_poissonMeasure
open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) =
      (r : ℝ) ^ 2 + (r : ℝ) := by
  have h0 := LevyStochCalc.Probability.integral_mul_eval_poissonMeasure r (1 : ℝ[X])
  have hfirst : (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = (r : ℝ) := by
    simpa using h0
  have h := LevyStochCalc.Probability.integral_mul_eval_poissonMeasure r X
  simp only [eval_X] at h
  rw [integral_add (LevyStochCalc.Probability.integrable_id_poissonMeasure r)
    (integrable_const 1), hfirst] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  rw [show (fun n : ℕ => (n : ℝ) ^ 2) = fun n : ℕ => (n : ℝ) * (n : ℝ) from by
    funext n
    ring]
  rw [h]
  ring
