-- Prove2me | solution 1 for Kyprianou.Ch01.expNegLogNatPow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:38:01.182721+00:00
-- url     : https://prove2.me/submissions/b8a9b28e-a5bd-45fb-8485-44398c6d9b7a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem solution
    (z : ℝ) (hz : 0 < z) (n : ℕ) :
    Real.exp (-(-Real.log z) * (n : ℝ)) = z ^ n := by
  calc
    Real.exp (-(-Real.log z) * (n : ℝ)) =
        Real.exp ((n : ℝ) * Real.log z) := by congr 1; ring
    _ = (Real.exp (Real.log z)) ^ n := by rw [Real.exp_nat_mul]
    _ = z ^ n := by rw [Real.exp_log hz]
