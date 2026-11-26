-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42DeficitCharacteristicV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:03:18.134711+00:00
-- url     : https://prove2.me/submissions/9c73c632-8ae3-466c-9cec-914bb68a8d71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_exercise42DeficitComplexRayV1
open MeasureTheory Set Complex AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The characteristic function of the source process from the imaginary deficit transform. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (L.X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) *
        (I * ((L.drift * ξ : ℝ) : ℂ) +
          ∫ y in Iio (0 : ℝ), (Complex.exp (I * ((ξ * y : ℝ) : ℂ)) - 1) ∂L.ν)) := by
  let z : ℂ := I * (ξ : ℂ)
  have hz : 0 ≤ z.re := by simp [z, Complex.mul_re]
  have h := Kyprianou.Ch04.exercise42DeficitComplexRayV1 P F L hBV t z hz
  rw [charFun_apply_real, integral_map L.adapted.measurable.aemeasurable (by fun_prop)]
  have hpoint (ω : Ω) : Complex.exp ((ξ : ℂ) * (L.X t ω : ℂ) * I) =
      Complex.exp (z * ((L.drift * (t : ℝ) : ℝ) : ℂ)) *
        Complex.exp (-z * ((L.drift * (t : ℝ) - L.X t ω : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [z, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  simp only [hpoint]
  rw [integral_const_mul, h, ← Complex.exp_add]
  congr 1
  have hi : (∫ y in Iio (0 : ℝ), (Complex.exp (I * ((ξ * y : ℝ) : ℂ)) - 1) ∂L.ν) =
      -(∫ y in Iio (0 : ℝ), (1 - Complex.exp (z * (y : ℂ))) ∂L.ν) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with y
    simp only [z, Complex.ofReal_mul]
    ring
  rw [hi]
  simp only [z, Complex.ofReal_mul]
  ring
