-- Prove2me | solution 1 for LevyStochCalc.Probability.measurableSet_stoppedSet
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:07:37.959023+00:00
-- url     : https://prove2.me/submissions/ed5d51b1-bcd2-4b85-81fb-4d72442919ec

import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F001

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

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


theorem _root_.solution {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) : MeasurableSet (stoppedSet τ) := by
  have hτm : Measurable τ := hτ.measurable'
  have hc : Measurable (fun p : Ω × ℝ => ((p.2 : ℝ) : WithTop ℝ)) :=
    WithTop.measurable_coe.comp measurable_snd
  exact measurableSet_le hc (hτm.comp measurable_fst)
