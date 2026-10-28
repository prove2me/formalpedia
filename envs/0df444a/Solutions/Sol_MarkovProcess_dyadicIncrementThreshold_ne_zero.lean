-- Prove2me | solution 1 for MarkovProcess.dyadicIncrementThreshold_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:19:48.907984+00:00
-- url     : https://prove2.me/submissions/ac8d2f21-2ea0-432b-b4c6-d0bf288a3456

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_FiniteGridFoundations
import Definitions.Def_MarkovProcess_DyadicIncrementScalars
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    dyadicIncrementThreshold γ n ≠ 0 := by
  unfold dyadicIncrementThreshold
  exact (ENNReal.rpow_eq_zero_iff_of_pos hγ).not.mpr (by simp)
