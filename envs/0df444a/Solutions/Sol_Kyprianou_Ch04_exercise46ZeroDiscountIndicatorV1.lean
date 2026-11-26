-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46ZeroDiscountIndicatorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:27:07.705188+00:00
-- url     : https://prove2.me/submissions/29d0eafc-9b28-4237-b29b-1886a0f1ee08

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
theorem solution
    (b : WithTop NNReal) :
    (if b = ⊤ then (0 : Real)
      else Real.exp (-0 * ((b.untopD 0 : NNReal) : Real))) =
      (if b = ⊤ then 0 else 1) := by
  simp
