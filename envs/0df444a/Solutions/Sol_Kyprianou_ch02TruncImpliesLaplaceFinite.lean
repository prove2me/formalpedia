-- Prove2me | solution 1 for Kyprianou.ch02TruncImpliesLaplaceFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:42:08.293401+00:00
-- url     : https://prove2.me/submissions/e2fe8184-16ad-4730-8292-13d0f2d3de07

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_oneSubExpUpperBound
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
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤ →
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) := by
  intro hTruncated φ hφ
  have hm : Measurable
      (fun x : E => ENNReal.ofReal (min 1 (f x))) := by
    fun_prop
  have hmax : 0 ≤ max (1 : ℝ) φ :=
    le_trans (by norm_num) (le_max_left 1 φ)
  have hbound :
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) ≤
      ENNReal.ofReal (max 1 φ) *
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) := by
    calc
      _ ≤ (∫⁻ x, ENNReal.ofReal (max 1 φ) *
          ENNReal.ofReal (min 1 (f x)) ∂η) := by
        refine lintegral_mono (fun x => ?_)
        have hu := Kyprianou.Ch02.oneSubExpUpperBound
          (f x) φ (hnonneg x) hφ
        have hc := ENNReal.ofReal_le_ofReal hu
        simpa only [ENNReal.ofReal_mul hmax] using hc
      _ = _ := lintegral_const_mul _ hm
  exact lt_of_le_of_lt hbound
    (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top) hTruncated)

