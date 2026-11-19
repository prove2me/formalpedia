-- Prove2me | solution 1 for LevyStochCalc.Probability.ProgressivelyMeasurable.of_isStronglyProgressive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:57:37.930055+00:00
-- url     : https://prove2.me/submissions/05c60339-7756-416d-a8f7-d545648f5b5a

import Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_isStronglyProgressive

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


theorem _root_.solution (h : IsStronglyProgressive ℱ fun s ω => H ω s) :
    ProgressivelyMeasurable ℱ H := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  let e : Ω × ℝ → Set.Iic t × Ω := fun p => (⟨min p.2 t, Set.mem_Iic.mpr (min_le_right _ _)⟩, p.1)
  have he : Measurable e :=
    ((measurable_snd.min measurable_const).subtype_mk).prodMk measurable_fst
  have : (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2)
      = (Set.univ ×ˢ Set.Iic t).indicator
        ((fun q : Set.Iic t × Ω => H q.2 q.1) ∘ e) := by
    funext p
    by_cases hp : p.2 ≤ t
    · simp [e, hp]
    · simp [e, hp]
  rw [this]
  exact ((h t).comp_measurable he).indicator (MeasurableSet.univ.prod measurableSet_Iic)
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
