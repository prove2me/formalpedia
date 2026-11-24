-- Prove2me | solution 1 for Kyprianou.Ch03.prod_expClock_discountMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:44:39.316324+00:00
-- url     : https://prove2.me/submissions/5987288b-bcba-4891-9a48-d78f093eeec8

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (tau : Omega → WithTop NNReal) (htau : Measurable tau)
    (q : ℝ) :
    Measurable (fun w => if tau w = ⊤ then (0 : ℝ)
      else Real.exp (-q * (((tau w).untopD (0 : NNReal) : NNReal) : ℝ))) := by
  have hf : Measurable (fun w => Real.exp (-q *
      (((tau w).untopD (0 : NNReal) : NNReal) : ℝ))) := by
    have h := htau.untopD (0 : NNReal)
    fun_prop
  exact Measurable.ite (measurableSet_eq_fun htau measurable_const)
    measurable_const hf
