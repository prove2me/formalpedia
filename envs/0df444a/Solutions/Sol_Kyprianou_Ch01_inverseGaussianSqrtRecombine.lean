-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianSqrtRecombine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:46:12.562983+00:00
-- url     : https://prove2.me/submissions/969fed54-daeb-4186-b5df-d989819c9299

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianBaseRootScale
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianComplexSqrtDouble
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianComplexTiltNonzero
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDoubleComplexTilt
open Complex Real ComplexOrder Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    -((Real.sqrt 2 : ℝ) : ℂ) *
      (((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) -
        Complex.sqrt (((b ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (theta : ℂ))) =
    Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
      2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
  let z : ℂ := ((b ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (theta : ℂ)
  have hz : z ≠ 0 :=
    Kyprianou.Ch01.inverseGaussianComplexTiltNonzero b hb theta
  have hDouble :=
    Kyprianou.Ch01.inverseGaussianComplexSqrtDouble z hz
  have hArg :=
    Kyprianou.Ch01.inverseGaussianDoubleComplexTilt b theta
  have hReal :=
    Kyprianou.Ch01.inverseGaussianBaseRootScale b hb
  have hCast : ((Real.sqrt 2 : ℝ) : ℂ) *
      ((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) = (b : ℂ) := by
    simpa only [Complex.ofReal_mul] using
      congrArg (fun t : ℝ => (t : ℂ)) hReal
  calc
    -((Real.sqrt 2 : ℝ) : ℂ) *
        (((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) -
          Complex.sqrt z) =
      ((Real.sqrt 2 : ℝ) : ℂ) * Complex.sqrt z -
        ((Real.sqrt 2 : ℝ) : ℂ) *
          ((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) := by ring
    _ = ((Real.sqrt 2 : ℝ) : ℂ) * Complex.sqrt z - (b : ℂ) := by
      rw [hCast]
    _ = Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
          2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
      have h := congrArg (fun t : ℂ => t - (b : ℂ)) hDouble
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) * Complex.sqrt z - (b : ℂ) =
          Complex.sqrt ((2 : ℂ) * z) - (b : ℂ) := h.symm
        _ = _ := by rw [hArg]
