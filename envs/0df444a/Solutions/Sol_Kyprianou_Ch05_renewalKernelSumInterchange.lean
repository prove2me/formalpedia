-- Prove2me | solution 1 for Kyprianou.Ch05.renewalKernelSumInterchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:21:36.551291+00:00
-- url     : https://prove2.me/submissions/aaf03df6-8ea6-4ac4-817d-eb9f34434d50

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

open Classical in
/-- Interchange the countable renewal-measure sum and the positive kernel integral. -/
theorem solution (F : Measure Real) (x : Real) (A B : Set Real) :
    (∑' n : Nat, ∫⁻ v in Set.Icc (0 : Real) x,
      (∫⁻ z in Set.Ioi (x - v),
        (if z - (x - v) ∈ A ∧ x - v ∈ B then (1 : ENNReal) else 0) ∂F)
      ∂(renewalConvolutionPower F n)) =
    renewalJointKernel (renewalMeasure F) F x A B := by
  unfold renewalJointKernel renewalMeasure
  rw [Measure.restrict_sum, lintegral_sum_measure]
  exact measurableSet_Icc
