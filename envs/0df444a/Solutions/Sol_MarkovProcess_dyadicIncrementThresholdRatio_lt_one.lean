-- Prove2me | solution 1 for MarkovProcess.dyadicIncrementThresholdRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:20:09.000608+00:00
-- url     : https://prove2.me/submissions/10e576da-9e6d-4d0c-b687-2d7ee050088f

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

theorem solution {γ : ℝ} (hγ : 0 < γ) :
    dyadicIncrementThresholdRatio γ < 1 := by
  unfold dyadicIncrementThresholdRatio
  exact ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ)
