-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41CorrectionExpansionV7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:19:46.605998+00:00
-- url     : https://prove2.me/submissions/c35c0b4d-a4c0-44f5-926c-b1bd05f36ab4

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    (α β : ℝ) (l : NNReal → ℝ) (t : NNReal) (Z : Finset NNReal) :
    α * (∑ s ∈ Z, if l s = 0 then (1 : ℝ) else 0) +
      β * ((if 0 < t then 1 else 0) + ∑ s ∈ Z, if s < t then 1 else 0) =
      (if 0 < t then β else 0) +
      ∑ s ∈ Z, ((if l s = 0 then α else 0) + (if s < t then β else 0)) := by
  simp only [mul_add, Finset.mul_sum, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib]
  ring
