-- Prove2me | solution 1 for MarkovProcess.dyadicIncrementThreshold_eq_ratio_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:20:01.734296+00:00
-- url     : https://prove2.me/submissions/fec5874e-1a3d-4d30-81d4-6cf51b4828ef

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

theorem solution (γ : ℝ) (n : ℕ) :
    dyadicIncrementThreshold γ n = dyadicIncrementThresholdRatio γ ^ n := by
  unfold dyadicIncrementThreshold dyadicIncrementThresholdRatio
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_neg,
    ← ENNReal.rpow_mul_natCast]
  congr 2
  ring
