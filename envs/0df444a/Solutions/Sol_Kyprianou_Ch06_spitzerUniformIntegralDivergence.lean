-- Prove2me | solution 1 for Kyprianou.Ch06.spitzerUniformIntegralDivergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:26:54.334287+00:00
-- url     : https://prove2.me/submissions/319cfce1-d0e5-4234-8272-b579a03f1957

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (μ : Measure ℝ) (f g : ℝ → ENNReal) (c : ENNReal)
    (hc0 : c ≠ 0) (hf : Measurable f)
    (hLower : ∀ t, c * f t ≤ g t)
    (hUpper : ∀ t, g t ≤ f t) :
    ((∫⁻ t, f t ∂μ) = ⊤ ↔ (∫⁻ t, g t ∂μ) = ⊤) := by
  have hlo : (∫⁻ t, c * f t ∂μ) ≤ (∫⁻ t, g t ∂μ) :=
    lintegral_mono hLower
  have hhi : (∫⁻ t, g t ∂μ) ≤ (∫⁻ t, f t ∂μ) :=
    lintegral_mono hUpper
  constructor
  · intro hfTop
    have htop : (∫⁻ t, c * f t ∂μ) = ⊤ := by
      rw [lintegral_const_mul c hf, hfTop, ENNReal.mul_top hc0]
    exact top_unique (htop ▸ hlo)
  · intro hgTop
    exact top_unique (hgTop ▸ hhi)
