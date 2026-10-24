-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.rpow_half_pow_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:37:09.550596+00:00
-- url     : https://prove2.me/submissions/bfbb42bc-4243-4a34-ad97-f4cdb8769482

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
/-- `((1/2)^α)^m ≤ 2^α · d^α` when `(1/2)^{m+1} < d`. Converts the geometric
level factor `r^m = ((1/2)^α)^m` into a Hölder factor in `d`. -/
lemma solution {α : ℝ} (hα : 0 < α) {d : ℝ} (m : ℕ)
    (hd : (1 / 2 : ℝ) ^ (m + 1) < d) :
    ((1 / 2 : ℝ) ^ α) ^ m ≤ (2 : ℝ) ^ α * d ^ α := by
  have hdpos : 0 < d := lt_of_le_of_lt (by positivity) hd
  have hstep : (1 / 2 : ℝ) ^ m < 2 * d := by
    have he : (1 / 2 : ℝ) ^ m = 2 * (1 / 2) ^ (m + 1) := by rw [pow_succ]; ring
    rw [he]; linarith
  have hr_eq : ((1 / 2 : ℝ) ^ α) ^ m = ((1 / 2 : ℝ) ^ m) ^ α := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ α) m,
        ← Real.rpow_natCast (1 / 2 : ℝ) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2), mul_comm]
  rw [hr_eq]
  calc ((1 / 2 : ℝ) ^ m) ^ α
      ≤ (2 * d) ^ α :=
        Real.rpow_le_rpow (by positivity) (le_of_lt hstep) (le_of_lt hα)
    _ = (2 : ℝ) ^ α * d ^ α := Real.mul_rpow (by norm_num) (le_of_lt hdpos)
