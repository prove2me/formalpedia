-- Prove2me | solution 1 for Kyprianou.Ch06.poissonZeroCountAsExponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:06:15.89075+00:00
-- url     : https://prove2.me/submissions/78af6c9d-4d04-46df-ae20-815b92d3a24c

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.Distributions.Poisson.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate t : NNReal) :
    ProbabilityTheory.poissonMeasure (t * rate) {0} =
      ENNReal.ofReal
        (Real.exp (-((rate : Real) * (t : Real)))) := by
  simp [ProbabilityTheory.poissonMeasure_singleton, mul_comm]
