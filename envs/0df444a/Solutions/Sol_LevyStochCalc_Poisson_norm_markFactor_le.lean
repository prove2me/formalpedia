-- Prove2me | solution 1 for LevyStochCalc.Poisson.norm_markFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:39:02.938824+00:00
-- url     : https://prove2.me/submissions/dfb7a105-bc7c-4565-b234-53e8472eb1c3

import Definitions.Def_LevyStochCalc_Poisson_CharacterMarkFactor_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The deterministic mark factor of the chain rule's integrand

At each time and mark the chain rule's integrand is the product of a deterministic factor,
carrying the indicator of the family and the jump `e^{i m} - 1` that a point there contributes,
with the exponential of the strict past. Inside the window the second factor agrees almost
surely with the character at that time, and so does the predictable representative of the
strict-past character.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section MarkFactor

variable (N : PoissonRandomMeasure P ν)


omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] in

theorem _root_.solution (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (q : ℝ × E) :
    ‖markFactor w Bfam q‖ ≤ 2 := by
  unfold markFactor
  by_cases h : q ∈ (⋃ j, Bfam j)
  · rw [Set.indicator_of_mem h]
    simp only [Complex.ofReal_one, one_mul]
    calc
      _ ≤ ‖Complex.exp (Complex.I * (↑(simpleMark w _ q) : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [Complex.norm_exp]; norm_num
  · rw [Set.indicator_of_notMem h]
    simp
