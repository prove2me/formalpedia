-- Prove2me | solution 1 for LevyStochCalc.Poisson.norm_charMark_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:39:22.812547+00:00
-- url     : https://prove2.me/submissions/1a8ee112-9cad-4e0b-8603-c93d5a4794b5

import Definitions.Def_LevyStochCalc_Poisson_CharacterFubini_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the compensator as a time integral of the pairings with the characters

The chain rule's integrand for the family cut at `t` factors as a deterministic mark times the
predictable exponential. Pairing a weight with the compensator and swapping the two integrals
therefore leaves, at each point of the window, the mark times the pairing of the weight with the
character at that time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Fubini


omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem _root_.solution (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (t : ℝ) (q : ℝ × E) :
    ‖charMark w Bfam t q‖ ≤ 2 := by
  unfold charMark
  by_cases h : q ∈ (⋃ j, truncFam Bfam t j)
  · rw [Set.indicator_of_mem h]
    simp only [Complex.ofReal_one, one_mul]
    calc
      _ ≤ ‖Complex.exp (Complex.I * (↑(simpleMark w _ q) : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [Complex.norm_exp]; norm_num
  · rw [Set.indicator_of_notMem h]
    simp
