-- Prove2me | solution 1 for LevyStochCalc.Probability.exitTime_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:13:27.683889+00:00
-- url     : https://prove2.me/submissions/e869e930-5820-4935-b6dc-8001e90bc2b2

import Definitions.Def_LevyStochCalc_Probability_ExitTime_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exit times of a process with continuous paths

`exitTime X k ω` is the first nonnegative time at which the path `X ω` has norm at least `k`, and
`⊤` when the path never reaches that norm. For continuous paths the comparison `exitTime X k ω ≤ t`
is decided by the values of the path on the rationals of `[0, t]`, so the exit time is a stopping
time for any filtration the process is adapted to. Letting `k` grow gives a localising sequence:
every time lies strictly below `exitTime X k` for all large `k`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]



theorem _root_.solution {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k t : ℝ) :
    exitTime X k ω ≤ (t : WithTop ℝ) ↔ ∃ s ∈ Set.Icc (0 : ℝ) t, k ≤ ‖X ω s‖ := by
  constructor
  · intro h
    by_cases hne : (exitSet X k ω).Nonempty
    · rw [exitTime, if_pos hne, WithTop.coe_le_coe] at h
      have hm := csInf_exitSet_mem hX hne
      exact ⟨sInf (exitSet X k ω), ⟨hm.1, h⟩, hm.2⟩
    · rw [exitTime, if_neg hne] at h
      exact absurd h (by simp)
  · rintro ⟨s, ⟨hs0, hst⟩, hk⟩
    have hmem : s ∈ exitSet X k ω := ⟨hs0, hk⟩
    have hne : (exitSet X k ω).Nonempty := ⟨s, hmem⟩
    rw [exitTime, if_pos hne, WithTop.coe_le_coe]
    exact (csInf_le (bddBelow_exitSet X k ω) hmem).trans hst

