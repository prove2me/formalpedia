-- Prove2me | solution 1 for Kyprianou.Ch05.karamataExpTiltMomentENN
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:49:24.964572+00:00
-- url     : https://prove2.me/submissions/f4f0ed0f-ff15-4c0c-8d75-de63a09107be

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Exponential tilt and compact image turn Laplace transforms into integer moments. -/
theorem solution
    (M : Measure Real) (n : Nat) :
    (∫⁻ z : Real, (ENNReal.ofReal z)^n ∂((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
      (fun z : Real => Real.exp (-z)))) =
      positiveLaplace M ((n : Real)+1) := by
  rw [lintegral_map (f := fun z : Real => (ENNReal.ofReal z)^n) (by fun_prop) (by fun_prop)]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  unfold positiveLaplace
  apply lintegral_congr
  intro z
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_nat_mul,← Real.exp_add]
  congr 2
  ring
