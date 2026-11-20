-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianGammaRootNormalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:39:55.703307+00:00
-- url     : https://prove2.me/submissions/4073197e-b808-49b6-808d-549636815808

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaScale
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianComplexSqrtDouble
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianBaseHalfPower
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianBaseRootScale
import Theorems.Thm_Kyprianou_Ch01_complexHalfLogPrincipalSqrt
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianComplexTiltNonzero
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDoubleComplexTilt
open Complex Real ComplexOrder Set Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (((Real.Gamma (-(1 / 2 : ℝ)) /
      Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) *
        (Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) -
         Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log ((((b ^ 2 / 2 : ℝ) : ℂ) -
            Complex.I * (theta : ℂ))))) =
    Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
      2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
  let z : ℂ := (((b ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (theta : ℂ))
  have hz : z ≠ 0 :=
    Kyprianou.Ch01.inverseGaussianComplexTiltNonzero b hb theta
  have hhalf : Complex.exp (((1 / 2 : ℝ) : ℂ) *
      Complex.log z) = Complex.sqrt z :=
    Kyprianou.Ch01.complexHalfLogPrincipalSqrt z hz
  have hroot := Kyprianou.Ch01.inverseGaussianBaseHalfPower b hb
  have hscale := Kyprianou.Ch01.inverseGaussianBaseRootScale b hb
  have hdouble := Kyprianou.Ch01.inverseGaussianComplexSqrtDouble z hz
  have harg : (2 : ℂ) * z =
      (((b ^ 2 : ℝ) : ℂ) - 2 * Complex.I * (theta : ℂ)) :=
    Kyprianou.Ch01.inverseGaussianDoubleComplexTilt b theta
  have hscale' : ((Real.sqrt 2 : ℝ) : ℂ) *
      ((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) = (b : ℂ) := by
    simpa only [Complex.ofReal_mul] using
      congrArg (fun t : ℝ => (t : ℂ)) hscale
  calc
    (((Real.Gamma (-(1 / 2 : ℝ)) /
      Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) *
        (Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) -
         Complex.exp (((1 / 2 : ℝ) : ℂ) * Complex.log z)) =
      -((Real.sqrt 2 : ℝ) : ℂ) *
        (((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) -
           Complex.sqrt z) := by
         rw [Kyprianou.Ch01.inverseGaussianGammaScale, hroot, hhalf]
           <;> simp only [Complex.ofReal_neg]
    _ = ((Real.sqrt 2 : ℝ) : ℂ) * Complex.sqrt z - (b : ℂ) := by
         calc
           -((Real.sqrt 2 : ℝ) : ℂ) *
                (((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) -
                   Complex.sqrt z) =
              ((Real.sqrt 2 : ℝ) : ℂ) * Complex.sqrt z -
                ((Real.sqrt 2 : ℝ) : ℂ) *
                  ((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) := by ring
           _ = _ := by rw [hscale']
    _ = Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
        2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
         simpa only [harg] using
           (congrArg (fun t : ℂ => t - (b : ℂ)) hdouble).symm
