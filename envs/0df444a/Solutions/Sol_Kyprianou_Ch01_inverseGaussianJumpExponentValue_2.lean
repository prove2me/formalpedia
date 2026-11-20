-- Prove2me | solution 2 for Kyprianou.Ch01.inverseGaussianJumpExponentValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:35:36.160312+00:00
-- url     : https://prove2.me/submissions/a3759908-6151-4262-9014-a1f7bf90a7f2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpGammaDifference
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaRootNormalisation
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
        Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
          2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
  intro Pi theta
  have hGamma :=
    Kyprianou.Ch01.inverseGaussianJumpGammaDifference b hb theta
  have hScale :=
    Kyprianou.Ch01.inverseGaussianGammaRootNormalisation b hb theta
  calc
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
        simpa only [Pi] using hGamma
    _ = Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
          2 * Complex.I * (theta : ℂ)) - (b : ℂ) := hScale
