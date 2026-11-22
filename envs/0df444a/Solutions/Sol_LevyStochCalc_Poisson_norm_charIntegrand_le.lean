-- Prove2me | solution 1 for LevyStochCalc.Poisson.norm_charIntegrand_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:39:22.962583+00:00
-- url     : https://prove2.me/submissions/ed048d5e-c649-4686-9f56-412d4225fb8f

import Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable integrand of the jump chain rule

For a simple integrand carried by a window of finite mark measure the integrand of the jump chain
rule has an exact predictable form: the strictly-past window sum is replaced by its predictable
representative and the deterministic factors are predictable because they are carried by the
window. The integrand is bounded by twice the indicator of the window, so its real and imaginary
parts are admissible for the compensated integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Integrand

variable (N : PoissonRandomMeasure P ν)


theorem _root_.solution (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ‖charIntegrand N w Bfam A T ω s e‖ ≤ 2 := by
  unfold charIntegrand
  by_cases h : (s,e) ∈ (⋃ j, Bfam j)
  · rw [Set.indicator_of_mem h]
    simp only [Complex.ofReal_one, one_mul, norm_mul, Complex.norm_exp,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
      mul_zero, sub_self, Real.exp_zero, mul_one]
    calc
      _ ≤ ‖Complex.exp (Complex.I * (↑(simpleMark w Bfam (s,e)) : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [Complex.norm_exp]; norm_num
  · rw [Set.indicator_of_notMem h]
    simp
