-- Prove2me | solution 1 for LevyStochCalc.Probability.ProgressivelyMeasurable.limsup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:57:26.334825+00:00
-- url     : https://prove2.me/submissions/b57d74a8-58bb-4ad0-82a1-e93d2edd6638

import Theorems.Thm_LevyStochCalc_Probability_MarkedProgressivelyMeasurable_stronglyMeasurable_setIntegral_integral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Progressively measurable real processes

`ProgressivelyMeasurable ℱ H` says that the process `H : Ω → ℝ → E`, viewed as a function of
`(ω, s)`, is `ℱ t ⊗ Borel`-measurable on the time window `s ≤ t`, for every `t`. This is
the progressive measurability of Mathlib's `IsStronglyProgressive`, phrased on `Ω × ℝ` by
truncating the time variable at `t`, which is the form in which the stochastic integrals of
this library consume it; `isStronglyProgressive` and `of_isStronglyProgressive` relate the
two.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}

section General

variable [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F]

namespace ProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

end ProgressivelyMeasurable

end General

section Mul

variable [TopologicalSpace E] [MulZeroClass E] [ContinuousMul E] {ℱ : Filtration ℝ mΩ}

end Mul

section Add

variable [NormedAddCommGroup E] {ℱ : Filtration ℝ mΩ}

end Add

section Integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

end Integral

section Marked

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]

namespace MarkedProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

end MarkedProgressivelyMeasurable

end Marked

section MarkedIntegral

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

end MarkedIntegral

/-! ### Countable suprema of real progressively measurable processes -/

section RealLimsup

variable {ℱ : Filtration ℝ mΩ}


theorem _root_.solution {H : ℕ → Ω → ℝ → ℝ}
    (h : ∀ k, ProgressivelyMeasurable ℱ (H k)) :
    ProgressivelyMeasurable ℱ fun ω s => Filter.limsup (fun k => H k ω s) Filter.atTop := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hind : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (fun s => Filter.limsup (fun k => H k p.1 s) Filter.atTop) p.2)
      = fun p : Ω × ℝ =>
        Filter.limsup (fun k => (Set.Iic t).indicator (H k p.1) p.2) Filter.atTop := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, Filter.limsup_const]
  rw [hind]
  refine stronglyMeasurable_iff_measurable.mpr (Measurable.limsup fun k => ?_)
  exact (h k t).measurable
end RealLimsup

end LevyStochCalc.Probability
