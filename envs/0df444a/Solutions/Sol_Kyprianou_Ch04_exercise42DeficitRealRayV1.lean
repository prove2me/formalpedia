-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42DeficitRealRayV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:53:44.434707+00:00
-- url     : https://prove2.me/submissions/30770994-efca-4ab0-8203-bb4cc4daaf67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
open MeasureTheory Set AvramDividend.Classical Complex
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual deficit Laplace law on the real ray, written in complex form. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (t : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ ω, Complex.exp (-(θ : ℂ) * ((L.drift * (t : ℝ) - L.X t ω : ℝ) : ℂ)) ∂P) =
      Complex.exp (-((t : ℝ) : ℂ) *
        ∫ y in Iio (0 : ℝ), (1 - Complex.exp ((θ : ℂ) * (y : ℂ))) ∂L.ν) := by
  have h := bv_actual_levy_drift_normalised_laplace L hBV t θ hθ
  have hL (ω : Ω) : Complex.exp (-(θ : ℂ) *
      ((L.drift * (t : ℝ) - L.X t ω : ℝ) : ℂ)) =
      ((Real.exp (θ * L.X t ω) * Real.exp (-((t : ℝ) * L.drift * θ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    norm_cast
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [hL]
  have hC : (∫ ω, ((Real.exp (θ * L.X t ω) * Real.exp (-((t : ℝ) * L.drift * θ)) : ℝ) : ℂ) ∂P) =
      ((∫ ω, Real.exp (θ * L.X t ω) * Real.exp (-((t : ℝ) * L.drift * θ)) ∂P : ℝ) : ℂ) := integral_ofReal
  rw [hC, h]
  have hI : (∫ y in Iio (0 : ℝ), (1 - Complex.exp ((θ : ℂ) * (y : ℂ))) ∂L.ν) =
      ((∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂L.ν : ℝ) : ℂ) := by
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp,
      ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact integral_ofReal
  rw [hI, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  congr 2
  ring
