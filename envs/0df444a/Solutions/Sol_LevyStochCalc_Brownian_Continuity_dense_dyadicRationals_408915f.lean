-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.dense_dyadicRationals_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:34:26.326311+00:00
-- url     : https://prove2.me/submissions/d4599b0a-38ad-4b6b-9f2e-28069e37ff64

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
/-- **Dyadic rationals are dense in ℝ.** Given any `x : ℝ` and any `r > 0`,
choose `n` with `(1/2)^n < r`, then `k := ⌊x · 2^n⌋`; the dyadic
`k · 2^(-n)` is within `r` of `x`. -/
lemma solution : Dense LevyStochCalc.Brownian.Continuity.dyadicRationals := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  set k : ℤ := ⌊x * (2 : ℝ)^n⌋ with hk_def
  set y : ℝ := (k : ℝ) * (2 : ℝ)^(-n : ℤ) with hy_def
  refine ⟨y, ?_, ?_⟩
  · rw [Metric.mem_ball]
    have h2n_pos : (0 : ℝ) < (2 : ℝ)^n := by positivity
    have h_pow_neg_eq : ((2 : ℝ) ^ (-n : ℤ)) = ((2 : ℝ)^n)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have h_floor_bound : x * (2 : ℝ)^n - 1 < (k : ℝ) ∧ (k : ℝ) ≤ x * (2 : ℝ)^n :=
      ⟨Int.sub_one_lt_floor _, Int.floor_le _⟩
    have h_diff : y - x = ((k : ℝ) - x * (2 : ℝ)^n) * ((2 : ℝ)^n)⁻¹ := by
      rw [hy_def, h_pow_neg_eq]; field_simp
    rw [Real.dist_eq, h_diff, abs_mul, abs_inv, abs_of_pos h2n_pos]
    have h_bound1 : |((k : ℝ) - x * (2 : ℝ)^n)| ≤ 1 := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · linarith [h_floor_bound.1]
      · linarith [h_floor_bound.2]
    have h_step : |((k : ℝ) - x * (2 : ℝ)^n)| * ((2 : ℝ)^n)⁻¹
        ≤ 1 * ((2 : ℝ)^n)⁻¹ := by
      apply mul_le_mul_of_nonneg_right h_bound1
      positivity
    rw [one_mul] at h_step
    refine lt_of_le_of_lt h_step ?_
    have h_inv_eq : ((2 : ℝ)^n)⁻¹ = (1 / 2 : ℝ)^n := by rw [one_div, inv_pow]
    rw [h_inv_eq]
    exact hn
  · exact ⟨k, n, rfl⟩
