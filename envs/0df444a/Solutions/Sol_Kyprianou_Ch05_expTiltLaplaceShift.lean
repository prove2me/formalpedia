-- Prove2me | solution 1 for Kyprianou.Ch05.expTiltLaplaceShift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:53:26.63433+00:00
-- url     : https://prove2.me/submissions/55e71dbc-2093-4a74-8fd5-7ffea8eec64e

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution (mu : Measure Real) (t : Real) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂
      (mu.withDensity (fun x => ENNReal.ofReal (Real.exp (-x))))) =
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(t+1)*x)) ∂mu := by
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring
