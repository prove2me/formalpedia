-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_cosine_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:43:22.463381+00:00
-- url     : https://prove2.me/submissions/f17c8e1b-1449-4c80-bd08-27f27329d63e

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Bounded cosine energy and square bound. -/
theorem solution (a x : ℝ) :
    let q := (1 - Real.cos (a*x)) / a^2
    0 ≤ q ∧ q ≤ 2/a^2 ∧ q^2 ≤ (2/a^2)*q := by
  dsimp
  have h0 : 0 ≤ (1 - Real.cos (a*x))/a^2 :=
    div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _)
  have h1 : (1 - Real.cos (a*x))/a^2 ≤ 2/a^2 :=
    div_le_div_of_nonneg_right (by linarith [Real.neg_one_le_cos (a*x)])
      (sq_nonneg _)
  refine ⟨h0,h1,?_⟩
  simpa only [pow_two] using mul_le_mul_of_nonneg_right h1 h0
