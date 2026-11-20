-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianJumpGammaDifference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:55:36.112235+00:00
-- url     : https://prove2.me/submissions/10e8ca48-7fe9-434e-8a46-b4fb63989828

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierWeightedIntegral
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaDifferenceRescaled
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    ∀ theta : ℝ,
      (∫ x in Set.Ioi (0 : ℝ),
        ((1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂Pi) =
      (((Real.Gamma (-(1 / 2 : ℝ)) /
        Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) *
        (Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) -
         Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log ((((b ^ 2 / 2 : ℝ) : ℂ) -
            Complex.I * (theta : ℂ))))) := by
  intro Pi theta
  have hW := Kyprianou.Ch01.inverseGaussianFourierWeightedIntegral b hb theta
  have hG := Kyprianou.Ch01.inverseGaussianGammaDifferenceRescaled b hb theta
  exact hW.trans hG
