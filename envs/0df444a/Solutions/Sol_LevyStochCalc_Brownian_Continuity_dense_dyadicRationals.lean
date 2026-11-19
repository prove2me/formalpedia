-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.dense_dyadicRationals
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:53:58.545561+00:00
-- url     : https://prove2.me/submissions/499f2b72-5539-4171-a5d4-b4202fbbd43e

import Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F000
import Mathlib.Topology.Algebra.Order.Floor

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
open LevyStochCalc.Brownian.Continuity

theorem solution : Dense dyadicRationals := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨((⌊x * (2 : ℝ) ^ n⌋ : ℤ) : ℝ) * (2 : ℝ) ^ (-n : ℤ), ?_, ⟨⌊x * (2 : ℝ) ^ n⌋, n, rfl⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hfl : (⌊x * (2 : ℝ) ^ n⌋ : ℝ) ≤ x * (2 : ℝ) ^ n := Int.floor_le _
  have hlt : x * (2 : ℝ) ^ n < (⌊x * (2 : ℝ) ^ n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hpow : (2 : ℝ) ^ (-n : ℤ) = (1 / 2 : ℝ) ^ n := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [hpow]
  constructor
  · have h1 : ((⌊x * (2 : ℝ) ^ n⌋ : ℤ) : ℝ) * (1 / 2 : ℝ) ^ n ≤ x := by
      calc ((⌊x * (2 : ℝ) ^ n⌋ : ℤ) : ℝ) * (1 / 2 : ℝ) ^ n
          ≤ (x * (2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n := by gcongr
        _ = x := by rw [mul_assoc, ← mul_pow]; norm_num
    linarith
  · have h2 : x - ((⌊x * (2 : ℝ) ^ n⌋ : ℤ) : ℝ) * (1 / 2 : ℝ) ^ n < (1 / 2 : ℝ) ^ n := by
      have : (x * (2 : ℝ) ^ n - (⌊x * (2 : ℝ) ^ n⌋ : ℝ)) * (1 / 2 : ℝ) ^ n < 1 * (1 / 2 : ℝ) ^ n := by
        gcongr
        linarith
      calc x - ((⌊x * (2 : ℝ) ^ n⌋ : ℤ) : ℝ) * (1 / 2 : ℝ) ^ n
          = (x * (2 : ℝ) ^ n - (⌊x * (2 : ℝ) ^ n⌋ : ℝ)) * (1 / 2 : ℝ) ^ n := by
            rw [sub_mul, mul_assoc, ← mul_pow]; norm_num
        _ < 1 * (1 / 2 : ℝ) ^ n := this
        _ = (1 / 2 : ℝ) ^ n := one_mul _
    linarith
