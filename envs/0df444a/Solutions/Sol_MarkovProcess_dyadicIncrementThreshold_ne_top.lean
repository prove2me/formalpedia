-- Prove2me | solution 1 for MarkovProcess.dyadicIncrementThreshold_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:19:55.297977+00:00
-- url     : https://prove2.me/submissions/4b4f6e38-8c2c-4e22-a84b-76dd6e8d2287

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
    dyadicIncrementThreshold γ n ≠ ∞ := by
  unfold dyadicIncrementThreshold
  exact (ENNReal.rpow_eq_top_iff_of_pos hγ).not.mpr (by simp)
