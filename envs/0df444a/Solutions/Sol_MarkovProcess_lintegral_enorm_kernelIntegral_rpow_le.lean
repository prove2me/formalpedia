-- Prove2me | solution 1 for MarkovProcess.lintegral_enorm_kernelIntegral_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:29:24.274494+00:00
-- url     : https://prove2.me/submissions/d48874e4-39d0-4ff1-99bf-cdbca074a0ef

import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_LpFinite_cf939c30
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-exponent contraction for sub-Markov kernels

This file proves the scalar subprobability estimate behind contraction of a
sub-Markov kernel on finite `Lᵖ` spaces, and its fibrewise integrated form.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]











end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-exponent contraction for sub-Markov kernels

This file proves the scalar subprobability estimate behind contraction of a
sub-Markov kernel on finite `Lᵖ` spaces, and its fibrewise integrated form.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]





namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution
    {μ : Measure α} {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hf : MemLp f p μ) :
    ∫⁻ x, ‖kernelIntegral κ f x‖ₑ ^ (p : ℝ) ∂μ
      ≤ ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ := by
  let : IsFiniteKernel κ := hκ.isFiniteKernel
  have hfComp : MemLp f p (κ ∘ₘ μ) := hf.mono_measure hκμ
  have hfFiber : ∀ᵐ x ∂μ, MemLp f p (κ x) := by
    have hFiberEq := Measure.ae_ae_of_ae_comp hfComp.1.ae_eq_mk
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast ne_of_gt (zero_lt_one.trans_le hp)
    have hpowInt := hfComp.integrable_norm_rpow hp0 ENNReal.coe_ne_top
    have hFiberInt := Measure.ae_integrable_of_integrable_comp hpowInt
    filter_upwards [hFiberEq, hFiberInt] with x hxEq hxInt
    have hxEq' : f =ᵐ[κ x] hfComp.1.mk f := hxEq
    have hxMeas : AEStronglyMeasurable f (κ x) :=
      hfComp.1.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq'.symm
    exact (integrable_norm_rpow_iff hxMeas hp0 ENNReal.coe_ne_top).mp hxInt
  calc
    ∫⁻ x, ‖kernelIntegral κ f x‖ₑ ^ (p : ℝ) ∂μ
        ≤ ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂κ x ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hfFiber] with x hx
          exact enorm_integral_rpow_le_lintegral_enorm_rpow hp (hκ x) hx
    _ = ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂(κ ∘ₘ μ) := by
          symm
          exact Measure.lintegral_bind (Kernel.aemeasurable κ)
            (hfComp.1.enorm.pow_const (p : ℝ))
    _ ≤ ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ :=
      lintegral_mono' hκμ le_rfl
