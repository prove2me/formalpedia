-- Prove2me | solution 1 for LevyStochCalc.Poisson.progressivelyMeasurable_comp_min
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:27:28.930334+00:00
-- url     : https://prove2.me/submissions/4bacb138-a5be-4de7-bb0d-6fa7c4b5cffe

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strict-past character as a progressively measurable process

The predictable representative of the strictly-past window sum, evaluated at a fixed mark of the
window and at the time clamped to the horizon, is a jointly measurable and progressively
measurable process. For a family carried strictly before the horizon it is exactly the exponent
of the strict-past character at every time, so the strict-past character is itself progressively
measurable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Evaluation


omit [IsProbabilityMeasure P] [SigmaFinite ν] in

theorem _root_.solution {f : Ω → ℝ → ℝ}
    (h : Probability.ProgressivelyMeasurable ℱ f) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => f ω (min s T) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  let g : Ω × ℝ → Ω × ℝ := fun p => (p.1, min p.2 T)
  have hg : Measurable g := measurable_fst.prodMk (measurable_snd.min measurable_const)
  have hS : MeasurableSet (Prod.snd ⁻¹' Set.Iic t : Set (Ω × ℝ)) :=
    measurable_snd measurableSet_Iic
  have hs := ((h t).comp_measurable hg).indicator hS
  convert hs using 1
  funext p
  by_cases hp : p.2 ≤ t
  · have hmin : min p.2 T ≤ t := (min_le_left _ _).trans hp
    simp [Set.indicator_apply, g, hp, hmin]
  · simp [Set.indicator_apply, hp]
