-- Prove2me | solution 1 for Kyprianou.Ch01.characteristicExponential_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:17:12.589867+00:00
-- url     : https://prove2.me/submissions/51ec5307-fb3f-4e9a-a22d-533439cd7589

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Characteristic-exponential normalisation gives expectation one. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ t : ℝ≥0,
      charFun (P.map (X t)) theta =
        Complex.exp (-((t : ℝ) : ℂ) * Psi))
    (t : ℝ≥0) :
    (∫ ω, Complex.exp
      (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
        ((t : ℝ) : ℂ) * Psi) ∂P) = 1 := by
  have hI :
      (∫ ω, Complex.exp (Complex.I * (theta : ℂ) *
        (X t ω : ℂ)) ∂P) =
        Complex.exp (-((t : ℝ) : ℂ) * Psi) := by
    rw [← hchar t, charFun_apply_real]
    rw [integral_map (hmeas t).aemeasurable (by fun_prop)]
    congr 1
    funext ω
    congr 1
    ring
  calc
    (∫ ω, Complex.exp
        (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
          ((t : ℝ) : ℂ) * Psi) ∂P) =
      (∫ ω, Complex.exp
        (Complex.I * (theta : ℂ) * (X t ω : ℂ)) ∂P) *
        Complex.exp (((t : ℝ) : ℂ) * Psi) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [Complex.exp_add]
    _ = 1 := by
      rw [hI, ← Complex.exp_add]
      simp
