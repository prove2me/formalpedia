-- Prove2me | solution 1 for LevyStochCalc.Probability.MarkedProgressivelyMeasurable.indicator_mark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:51:30.133954+00:00
-- url     : https://prove2.me/submissions/fa1155af-3142-4ba3-b5cc-06417af5c780

import Definitions.Def_LevyStochCalc_Probability_Progressive_F001
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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


theorem _root_.solution (h : MarkedProgressivelyMeasurable ℱ φ) {S : Set E}
    (hS : MeasurableSet S) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => S.indicator (fun _ => φ ω s e) e := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => S.indicator (fun _ => φ p.1 s p.2.2) p.2.2) p.2.1)
      = {p : Ω × ℝ × E | p.2.2 ∈ S}.indicator
        (fun p => (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1) := by
    funext p
    by_cases hp : p.2.2 ∈ S
    · simp [hp]
    · simp [hp]
  rw [this]
  exact (h t).indicator (measurable_snd.snd hS)
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
