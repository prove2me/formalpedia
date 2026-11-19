-- Prove2me | solution 1 for LevyStochCalc.Probability.ProgressivelyMeasurable.stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:52:22.170992+00:00
-- url     : https://prove2.me/submissions/da9f041e-d972-443a-bd39-686c34f5ed2f

import Theorems.Thm_LevyStochCalc_Probability_MarkedProgressivelyMeasurable_indicator_mark
import Theorems.Thm_LevyStochCalc_Probability_MarkedProgressivelyMeasurable_stronglyMeasurable_setIntegral_integral
import Theorems.Thm_LevyStochCalc_Probability_MarkedProgressivelyMeasurable_stronglyMeasurable_setIntegral_prod
import Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_isStronglyProgressive
import Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_limsup
import Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_minTime
import Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_of_isStronglyProgressive
import Theorems.Thm_LevyStochCalc_Probability_measurableSet_stoppedRegion

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a progressively measurable process

Cutting a process off at a stopping time keeps it progressively measurable: before a time `t` the
region `{(ω, s) : s ≤ t, s ≤ τ ω}` is the complement, inside `Ω × (-∞, t]`, of a countable union
of rectangles `{τ ≤ q} × (q, t]` over the rationals, each measurable for the σ-algebra at `t`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


theorem _root_.solution {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hH : ProgressivelyMeasurable ℱ H) :
    ProgressivelyMeasurable ℱ (LevyStochCalc.Probability.stopped τ H) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have key : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (LevyStochCalc.Probability.stopped τ H p.1) p.2)
      = Set.indicator (stoppedRegion τ t)
        (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    by_cases h1 : p ∈ stoppedRegion τ t
    · obtain ⟨h1a, h1b⟩ := h1
      rw [Set.indicator_of_mem (show p ∈ stoppedRegion τ t from ⟨h1a, h1b⟩),
        Set.indicator_of_mem (show p.2 ∈ Set.Iic t from h1a),
        Set.indicator_of_mem (show p.2 ∈ Set.Iic t from h1a),
        LevyStochCalc.Probability.stopped, if_pos h1b]
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : p.2 ∈ Set.Iic t
      · have h3 : ¬ ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1 := fun hc => h1 ⟨h2, hc⟩
        rw [Set.indicator_of_mem h2, LevyStochCalc.Probability.stopped, if_neg h3]
      · rw [Set.indicator_of_notMem h2]
  rw [key]
  exact (hH t).indicator (measurableSet_stoppedRegion hτ t)
end LevyStochCalc.Probability
