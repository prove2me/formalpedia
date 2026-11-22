-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.le_clipTime_iff
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T07:04:35.657526+00:00
-- url     : https://prove2.me/submissions/5ed30eae-6486-4fc6-b423-8b7511f841d5

import Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}


theorem _root_.solution {s : ℝ} (hs : s ≤ t) :
    ((s : ℝ) : WithTop ℝ) ≤ τ ω ↔ s ≤ clipTime τ t ω := by
  by_cases h : τ ω = ⊤
  · rw [clipTime_eq_self_of_top h, h]
    simp [hs]
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
    rw [clipTime_eq_min hr.symm, ← hr]
    simp [le_min_iff, hs]
