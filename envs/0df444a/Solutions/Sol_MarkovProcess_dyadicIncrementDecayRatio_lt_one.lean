-- Prove2me | solution 1 for MarkovProcess.dyadicIncrementDecayRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:19:42.744588+00:00
-- url     : https://prove2.me/submissions/7ceb50d6-8f65-4630-a4e7-f924db755916

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

theorem solution {p q γ : ℝ} (hp : 0 < p)
    (hγ : γ < (q - 1) / p) : dyadicIncrementDecayRatio p q γ < 1 := by
  have hmul : p * γ < q - 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hp).mp hγ
  have hexp : 1 - q + p * γ < 0 := by
    linarith only [hmul]
  exact NNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
