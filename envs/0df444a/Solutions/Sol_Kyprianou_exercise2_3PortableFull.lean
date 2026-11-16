-- Prove2me | solution 1 for Kyprianou.exercise2_3PortableFull
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:37:32.1912+00:00
-- url     : https://prove2.me/submissions/8524cdd5-de00-40b1-b30c-d8503c2bb807

import Mathlib
import Theorems.Thm_Kyprianou_ch02LaplaceFiniteImpliesTrunc
import Theorems.Thm_Kyprianou_ch02TruncImpliesLaplaceFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou

theorem solution
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) ↔
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤ := by
  constructor
  case mp =>
    intro h
    exact Kyprianou.ch02LaplaceFiniteImpliesTrunc η f hf hnonneg h
  case mpr =>
    intro h
    exact Kyprianou.ch02TruncImpliesLaplaceFinite η f hf hnonneg h

