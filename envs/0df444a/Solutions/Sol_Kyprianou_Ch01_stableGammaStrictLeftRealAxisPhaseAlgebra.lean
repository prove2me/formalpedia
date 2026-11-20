-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftRealAxisPhaseAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T13:11:15.99484+00:00
-- url     : https://prove2.me/submissions/45a98724-a74e-4e37-b089-ba984d2d4ed1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter Kyprianou.Ch01
set_option autoImplicit false

theorem solution (alpha u : ℝ) (hu : 0 < u) :
    (((((1 / u) ^ (1 - alpha)) * Real.Gamma (1 - alpha) : ℝ)) : ℂ) =
      ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
        Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (u : ℂ))
    := by
  have hp : (1 / u) ^ (1 - alpha) = u ^ (alpha - 1) := by
    calc
      (1 / u) ^ (1 - alpha) = u⁻¹ ^ (1 - alpha) := by rw [one_div]
      _ = u ^ (-(1 - alpha)) :=
        (Real.rpow_neg_eq_inv_rpow u (1 - alpha)).symm
      _ = u ^ (alpha - 1) := by congr 1 <;> ring
  rw [hp, Complex.ofReal_mul, Complex.ofReal_cpow hu.le,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
  ring
