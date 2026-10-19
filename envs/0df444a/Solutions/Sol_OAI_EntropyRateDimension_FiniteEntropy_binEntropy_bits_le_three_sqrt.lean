-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.binEntropy_bits_le_three_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:25:28.805884+00:00
-- url     : https://prove2.me/submissions/325af2c7-c338-408b-94dd-574bd1f07adb

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.binEntropy q / Real.log 2 ≤ 3 * Real.sqrt q := by
  have hl2 : (2/3:ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlpos : 0 < Real.log 2 := by linarith
  rw [div_le_iff₀ hlpos, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  set x := Real.sqrt q with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg q
  have hqx : q = x ^ 2 := (Real.sq_sqrt hq).symm
  have h1 : Real.negMulLog q ≤ 2 * x - 2 * q := by
    rcases hx0.eq_or_lt with h | h
    · have : q = 0 := by rw [hqx, ← h]; ring
      rw [this]; simp; exact hx0
    · have hlog : -Real.log x ≤ 1 / x - 1 := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 / x by positivity)
        rw [one_div, Real.log_inv] at this; rwa [one_div]
      rw [Real.negMulLog, hqx, Real.log_pow]; push_cast
      have : x ^ 2 * (1 / x - 1) = x - x^2 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hlog (sq_nonneg x)]
  have h2 : Real.negMulLog (1 - q) ≤ q := by
    rcases (sub_nonneg.mpr hq1).eq_or_lt with h | h
    · rw [← h]; simp; exact hq
    · have := Real.one_sub_inv_le_log_of_pos h
      rw [Real.negMulLog]
      have e : (1 - q) * (1 - (1 - q)⁻¹) = -q := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left this h.le]
  nlinarith [mul_le_mul_of_nonneg_right hl2.le hx0]

