-- Prove2me | solution 1 for LevyStochCalc.Probability.norm_le_of_le_exitTime
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:53:18.586154+00:00
-- url     : https://prove2.me/submissions/507c67ef-9e1d-4713-88d3-a701d8a7e5d1

import Definitions.Def_LevyStochCalc_Probability_ExitTime_F001

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



theorem _root_.solution {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k s : ℝ}
    (hs : 0 < s) (hle : (s : WithTop ℝ) ≤ exitTime X k ω) : ‖X ω s‖ ≤ k := by
  by_contra hcon
  have hlt : k < ‖X ω s‖ := lt_of_not_ge hcon
  have hopen : IsOpen {r : ℝ | k < ‖X ω r‖} := isOpen_lt continuous_const hX.norm
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen s hlt
  set r := s - min δ s / 2 with hr
  have hmin0 : 0 < min δ s := lt_min hδ hs
  have hminle : min δ s ≤ s := min_le_right _ _
  have hminδ : min δ s ≤ δ := min_le_left _ _
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrs : r < s := by rw [hr]; linarith
  have hrball : r ∈ Metric.ball s δ := by
    rw [Metric.mem_ball, Real.dist_eq, hr, abs_of_neg (by linarith)]; linarith
  have hrk : k < ‖X ω r‖ := hball hrball
  have hrmem : r ∈ exitSet X k ω := ⟨hr0, hrk.le⟩
  unfold exitTime at hle
  rw [if_pos ⟨r, hrmem⟩] at hle
  have h1 : sInf (exitSet X k ω) ≤ r := csInf_le (bddBelow_exitSet X k ω) hrmem
  have h2 : s ≤ sInf (exitSet X k ω) := WithTop.coe_le_coe.1 hle
  linarith
