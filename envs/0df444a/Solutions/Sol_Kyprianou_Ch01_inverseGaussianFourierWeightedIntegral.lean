-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFourierWeightedIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:30:32.101515+00:00
-- url     : https://prove2.me/submissions/92ce2d1a-12a5-43b2-b637-6f55427212c5

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierWithDensity
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierPointwiseGamma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    ∀ theta : ℝ,
      (∫ x in Set.Ioi (0 : ℝ), ((1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂Pi) =
      (((1 / Real.sqrt (2 * Real.pi) : ℝ)) : ℂ) * (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) - Complex.exp ((((-(b ^ 2 / 2) : ℝ) : ℂ) +
            Complex.I * (theta : ℂ)) * (r : ℂ))) *
          ((r ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) ∂volume) := by
  intro Pi theta
  have hD := Kyprianou.Ch01.inverseGaussianFourierWithDensity b hb theta
  calc
    (∫ x in Set.Ioi (0 : ℝ),
       ((1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂Pi) =
      ∫ x in Set.Ioi (0 : ℝ),
        ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
          Real.exp (-(b ^ 2 * x / 2))) •
        ((1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂volume := by
        simpa only [Pi] using hD
    _ = ∫ r in Set.Ioi (0 : ℝ),
      ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      ((Complex.exp (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) -
        Complex.exp ((((-(b ^ 2 / 2) : ℝ) : ℂ) +
          Complex.I * (theta : ℂ)) * (r : ℂ))) *
          ((r ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        exact Kyprianou.Ch01.inverseGaussianFourierPointwiseGamma
          b theta r hr
    _ = _ := by rw [integral_const_mul]
