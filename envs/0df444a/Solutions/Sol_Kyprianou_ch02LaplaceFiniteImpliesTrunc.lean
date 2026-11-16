-- Prove2me | solution 1 for Kyprianou.ch02LaplaceFiniteImpliesTrunc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:47:19.114895+00:00
-- url     : https://prove2.me/submissions/e2dac46a-2a27-4a93-a419-424a37f7e293

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_oneSubExpLowerBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

open Kyprianou

theorem solution
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) →
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤ := by
  intro hLaplace
  have hm : Measurable (fun x : E => ENNReal.ofReal
      (1 - Real.exp (-f x))) := by
    fun_prop
  have hbound : (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) ≤
      (2 : ENNReal) *
      (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-f x)) ∂η) := by
    calc
      _ ≤ (∫⁻ x, (2 : ENNReal) *
          ENNReal.ofReal (1 - Real.exp (-f x)) ∂η) := by
        refine lintegral_mono (fun x => ?_)
        have hh := Kyprianou.Ch02.oneSubExpLowerBound (f x) (hnonneg x)
        have hc := ENNReal.ofReal_le_ofReal hh
        simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using hc
      _ = _ := lintegral_const_mul 2 hm
  exact lt_of_le_of_lt hbound
    (ENNReal.mul_lt_top (by norm_num) (by
      simpa only [neg_mul, one_mul] using
        (hLaplace 1 (by norm_num))))

