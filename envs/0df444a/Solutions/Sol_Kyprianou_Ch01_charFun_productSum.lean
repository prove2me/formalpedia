-- Prove2me | solution 1 for Kyprianou.Ch01.charFun_productSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:00:54.845976+00:00
-- url     : https://prove2.me/submissions/d6aa3a76-fcb8-4d9c-9a03-5566d83e843b

import Mathlib.Probability.Independence.CharacteristicFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem solution
    (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (xi : ℝ) :
    charFun ((mu.prod nu).map (fun p : ℝ × ℝ => p.1 + p.2)) xi =
      charFun mu xi * charFun nu xi := by
  simpa only [Pi.mul_apply] using
    congrFun (ProbabilityTheory.charFun_map_add_prod_eq_mul
      (μ := mu) (ν := nu)) xi
