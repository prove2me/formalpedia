-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42NegativeUncompensatedExponentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:02:05.441181+00:00
-- url     : https://prove2.me/submissions/64627166-b046-4b43-8366-8067742a2ee7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_negativeCompensationLedgerV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
open MeasureTheory ProbabilityTheory Set Complex AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uncompensated form of the original BV characteristic exponent. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (ξ : ℝ) :
    ∃ hν : IsLevyMeasure L.ν,
    Kyprianou.Ch01.levyTripleExponent ⟨L.c, 0, L.ν, hν⟩ ξ =
      I * ((L.drift * ξ : ℝ) : ℂ) +
      ∫ y in Iio (0 : ℝ), (Complex.exp (I * ((ξ * y : ℝ) : ℂ)) - 1) ∂L.ν := by
  have hν : IsLevyMeasure L.ν :=
    ⟨measure_mono_null (show ({0} : Set ℝ) ⊆ Ici 0 by simp) L.ν_Ici, L.ν_integrable⟩
  refine ⟨hν, ?_⟩
  have hn : ∀ᵐ y ∂L.ν, y < 0 := by
    rw [ae_iff]
    have he : {y : ℝ | ¬ y < 0} = Ici (0 : ℝ) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_Ici, not_lt]
    rw [he]
    exact L.ν_Ici
  have hr : L.ν.restrict (Iio 0) = L.ν := Measure.restrict_eq_self_of_ae_mem hn
  have hint := boundedVariation_min_one_abs_integrable L hBV
  rw [IntegrableOn, hr] at hint
  let l : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator id
  have hc := integrable_levyCompensatedIntegrand hν ξ
  obtain ⟨hlc, heq⟩ := Kyprianou.Ch04.negativeCompensationLedgerV1 L.ν hn hint ξ
  have hsum := integral_congr_ae heq
  rw [integral_add hc hlc, integral_mul_const, integral_mul_const, integral_complex_ofReal] at hsum
  have hli : ∫ y, l y ∂L.ν = ∫ y in Ioo (-1 : ℝ) 0, y ∂L.ν :=
    integral_indicator measurableSet_Ioo
  rw [hli] at hsum
  rw [Kyprianou.Ch01.levyTripleExponent, hr, hsum]
  simp only [NNReal.coe_zero, Complex.ofReal_zero, zero_mul, zero_div, sub_zero]
  unfold SpectrallyNegativeLevy.drift
  push_cast
  ring
