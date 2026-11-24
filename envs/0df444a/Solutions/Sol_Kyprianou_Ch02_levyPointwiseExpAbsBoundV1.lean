-- Prove2me | solution 1 for Kyprianou.Ch02.levyPointwiseExpAbsBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:24:40.971181+00:00
-- url     : https://prove2.me/submissions/5696712f-399e-4b35-a971-2e423c6ccde8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (x : ℝ) : min 1 |x| ≤ 2 * (1 - Real.exp (-|x|)) := by
  have hp := Real.exp_pos |x|
  have h := Real.add_one_le_exp |x|
  have hh : Real.exp (-|x|) * (1 + |x|) ≤ 1 := by
    rw [Real.exp_neg, inv_mul_le_iff₀ hp]
    linarith
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
  rcases le_total |x| 1 with ha | ha
  · rw [min_eq_right ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr he)]
  · rw [min_eq_left ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (Real.exp_nonneg (-|x|))]
