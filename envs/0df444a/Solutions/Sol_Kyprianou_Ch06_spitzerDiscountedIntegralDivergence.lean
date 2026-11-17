-- Prove2me | solution 1 for Kyprianou.Ch06.spitzerDiscountedIntegralDivergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:37:53.55983+00:00
-- url     : https://prove2.me/submissions/f6233d43-6d2f-4055-abe0-d031fa4322fb

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_spitzerExponentialWeightBounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    (f : ℝ → ENNReal) (hf : Measurable f)
    (p : ℝ) (hp : 0 ≤ p) :
    ((∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (Real.exp (-p * t)) * f t ∂volume) = ⊤ ↔
    (∫⁻ t in Set.Ioo (0 : ℝ) 1, f t ∂volume) = ⊤) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let c : ENNReal := ENNReal.ofReal (Real.exp (-p))
  have hc : c ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hBounds : ∀ᵐ t ∂μ,
      c * f t ≤ ENNReal.ofReal (Real.exp (-p * t)) * f t ∧
      ENNReal.ofReal (Real.exp (-p * t)) * f t ≤ f t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    obtain ⟨hlo, hhi⟩ :=
      Kyprianou.Ch06.spitzerExponentialWeightBounds p t hp
        (le_of_lt ht.1) (le_of_lt ht.2)
    constructor
    · exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hlo)
          (show (0 : ENNReal) ≤ f t from zero_le)
    · calc
        ENNReal.ofReal (Real.exp (-p * t)) * f t ≤ 1 * f t := by
          apply mul_le_mul_of_nonneg_right
          · simpa using (ENNReal.ofReal_le_ofReal hhi)
          · exact (show (0 : ENNReal) ≤ f t from zero_le)
        _ = f t := one_mul _
  have hLower : c * (∫⁻ t, f t ∂μ) ≤
      (∫⁻ t, ENNReal.ofReal (Real.exp (-p * t)) * f t ∂μ) := by
    rw [← lintegral_const_mul c hf]
    exact lintegral_mono_ae (hBounds.mono fun t ht => ht.1)
  have hUpper :
      (∫⁻ t, ENNReal.ofReal (Real.exp (-p * t)) * f t ∂μ) ≤
      (∫⁻ t, f t ∂μ) :=
    lintegral_mono_ae (hBounds.mono fun t ht => ht.2)
  change ((∫⁻ t, ENNReal.ofReal (Real.exp (-p * t)) * f t ∂μ) = ⊤) ↔
    ((∫⁻ t, f t ∂μ) = ⊤)
  constructor
  · intro hw
    exact top_unique (hw ▸ hUpper)
  · intro hfTop
    have htop : c * (∫⁻ t, f t ∂μ) = ⊤ := by
      rw [hfTop, ENNReal.mul_top hc]
    exact top_unique (htop ▸ hLower)
