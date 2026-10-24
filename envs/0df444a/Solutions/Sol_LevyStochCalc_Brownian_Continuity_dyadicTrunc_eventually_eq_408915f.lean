-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:35:42.005642+00:00
-- url     : https://prove2.me/submissions/c1a612bd-34e8-4b64-bafe-7206ea5575c9

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Continuity
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc.Brownian.Continuity in
/-- A dyadic rational coincides with its own level-`L` truncation for all
sufficiently large `L`. -/
lemma solution {s : ℝ} (hs : s ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → LevyStochCalc.Brownian.Continuity.dyadicTrunc L s = s := by
  obtain ⟨k, n, hkn⟩ := hs
  refine ⟨n, fun L hL => ?_⟩
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - n) * (2 : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hL]
  have hsL : s * 2 ^ L = ((k * 2 ^ (L - n) : ℤ) : ℝ) := by
    rw [hkn, zpow_neg, zpow_natCast, hpow]
    push_cast
    field_simp
  rw [LevyStochCalc.Brownian.Continuity.dyadicTrunc, hsL, Int.floor_intCast, hkn, zpow_neg, zpow_natCast, hpow]
  push_cast
  field_simp
