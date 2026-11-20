-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFourierExpDifference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:47:36.724189+00:00
-- url     : https://prove2.me/submissions/2c897751-4752-4bb7-b900-5157e191668a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real
set_option autoImplicit false

theorem solution (b theta r : ℝ) :
    ((1 : ℂ) - Complex.exp (Complex.I * ((theta * r : ℝ) : ℂ))) *
      ((Real.exp (-(b ^ 2 * r / 2)) : ℝ) : ℂ) =
    Complex.exp (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) -
      Complex.exp ((((-(b ^ 2 / 2) : ℝ) : ℂ) +
        Complex.I * (theta : ℂ)) * (r : ℂ)) := by
  have heq :
      (((-(b ^ 2 / 2) : ℝ) : ℂ) + Complex.I * (theta : ℂ)) * (r : ℂ) =
      (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) +
        Complex.I * ((theta * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.exp_add]
  simp only [Complex.ofReal_exp]
  push_cast
  ring
