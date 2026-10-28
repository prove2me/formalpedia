-- Prove2me | solution 2 for MarkovProcess.measurable_laplaceDensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:55:56.114876+00:00
-- url     : https://prove2.me/submissions/46ce0fae-67fe-4b09-a4bf-a725ccafafab

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- Source: MarkovProcess/Killed/GluingPotential.lean:47-51 at pinned commit. -/
theorem solution (lam : ℝ) :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-lam * t)) :=
  ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
