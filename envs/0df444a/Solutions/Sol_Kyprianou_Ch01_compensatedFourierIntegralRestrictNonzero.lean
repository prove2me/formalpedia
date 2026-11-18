-- Prove2me | solution 1 for Kyprianou.Ch01.compensatedFourierIntegralRestrictNonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:13:38.615587+00:00
-- url     : https://prove2.me/submissions/f5732bba-0e4e-437c-82ae-e659c073c721

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex
set_option autoImplicit false
/-! Removing the atom at zero does not change the compensated Fourier integral. -/
theorem solution
    (μ : Measure ℝ) [IsFiniteMeasure μ] (xi : ℝ) :
    (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1)
        ∂(μ.restrict ({0}ᶜ))) =
    ∫ x : ℝ, (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂μ := by
  change (∫ x in ({0}ᶜ : Set ℝ),
    (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂μ) = _
  rw [← integral_indicator (measurableSet_singleton (0 : ℝ)).compl]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x = 0
  · subst x
    simp
  · simp [Set.indicator_of_mem, hx]
