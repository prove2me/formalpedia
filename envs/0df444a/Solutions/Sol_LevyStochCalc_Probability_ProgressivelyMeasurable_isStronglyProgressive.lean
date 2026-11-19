-- Prove2me | solution 1 for LevyStochCalc.Probability.ProgressivelyMeasurable.isStronglyProgressive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:57:14.895904+00:00
-- url     : https://prove2.me/submissions/28d13f80-538a-44a2-a925-cf6e14734de5

import Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_minTime

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


theorem _root_.solution (h : ProgressivelyMeasurable ℱ H) :
    IsStronglyProgressive ℱ fun s ω => H ω s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have he : Measurable fun q : Set.Iic t × Ω => (q.2, (q.1 : ℝ)) :=
    measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst)
  have := (h t).comp_measurable he
  have heq : (fun q : Set.Iic t × Ω => H q.2 q.1)
      = (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) ∘ fun q : Set.Iic t × Ω =>
        (q.2, (q.1 : ℝ)) := by
    funext q
    exact (Set.indicator_of_mem q.1.2 _).symm
  rw [heq]
  exact this
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

end RealLimsup

end LevyStochCalc.Probability
