-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.exists_dyadic_scale_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:37:08.322093+00:00
-- url     : https://prove2.me/submissions/289a5bda-c63f-451b-a0ec-d9f3ce6e4e7e

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
/-- **Dyadic scale selection.** For `0 < d ≤ 1` there is `m` with
`(1/2)^{m+1} < d ≤ (1/2)^m`. -/
lemma solution {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) < d ∧ d ≤ (1 / 2) ^ m := by
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < d :=
    exists_pow_lt_of_lt_one hd0 (by norm_num)
  classical
  have hspec : (1 / 2 : ℝ) ^ Nat.find hex < d := Nat.find_spec hex
  have hpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h] at hspec; simp at hspec; linarith
    · exact h
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel hpos]; exact hspec
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [not_lt] at hmin
    exact hmin
