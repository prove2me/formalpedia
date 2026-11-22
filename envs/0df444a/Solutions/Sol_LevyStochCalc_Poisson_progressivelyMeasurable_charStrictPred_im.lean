-- Prove2me | solution 1 for LevyStochCalc.Poisson.progressivelyMeasurable_charStrictPred_im
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:34:39.753613+00:00
-- url     : https://prove2.me/submissions/31e6739b-0a4f-4dfa-aece-b167cfb886cc

import Theorems.Thm_LevyStochCalc_Poisson_progressivelyMeasurable_comp_min
import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F001

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

end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}

variable (hℱ : IsPoissonFiltration N ℱ) (hBm : ∀ j, MeasurableSet (Bfam j))
  (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)


include hℱ hBm hA hAν in

theorem _root_.solution (T : ℝ) (e₀ : E) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (charStrictPred N w Bfam A T e₀ s ω).im := by
  have hm : Probability.MarkedProgressivelyMeasurable ℱ
      (predStrict N w Bfam A T) := by
    have hh := markedPredictable_predStrict N hℱ w hBm hA hAν T
    exact?
  have hf := progressivelyMeasurable_eval_mark hm e₀
  have hg := progressivelyMeasurable_comp_min hf T
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hs : MeasurableSet (Prod.snd ⁻¹' Set.Iic t : Set (Ω × ℝ)) :=
    measurable_snd measurableSet_Iic
  have hj := (Real.continuous_sin.comp_stronglyMeasurable (hg t)).indicator hs
  convert hj using 1
  funext p
  by_cases h : p.2 ≤ t <;>
    simp [Set.indicator_apply, h, charStrictPred, Complex.exp_im]
