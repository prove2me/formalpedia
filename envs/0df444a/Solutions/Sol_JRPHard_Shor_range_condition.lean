-- Prove2me | solution 1 for JRPHard.Shor.range_condition
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T12:04:49.780921+00:00
-- url     : https://prove2.me/submissions/590b3d74-cd17-4f62-b32b-1b1f410ce55f

import Definitions.Def_JRPHard_Shor_Setting
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open JRPHard.Shor

theorem solution {n : ℕ} (B : ℕ) (a : Fin n → ℕ)
    (hlam : (2 : ℝ) ^ (scale B / 2) + (2 : ℝ) ^ (-(scale B / 2)) <
      2 * Real.sqrt 2) :
    lowL B a + highU B a <
      2 * Real.sqrt (2 * lowL B a * highU B a) := by
  let z : ℝ := (2 : ℝ) ^ (scale B * halfSum a)
  have hz : 0 < z := Real.rpow_pos_of_pos (by norm_num) _
  have hL : lowL B a = z * (2 : ℝ) ^ (-(scale B / 2)) := by
    dsimp [lowL, z]
    rw [show scale B * (halfSum a - 1 / 2) =
      scale B * halfSum a + -(scale B / 2) by ring]
    exact Real.rpow_add (by norm_num) _ _
  have hU : highU B a = z * (2 : ℝ) ^ (scale B / 2) := by
    dsimp [highU, z]
    rw [show scale B * (halfSum a + 1 / 2) =
      scale B * halfSum a + scale B / 2 by ring]
    exact Real.rpow_add (by norm_num) _ _
  have hrecip : (2 : ℝ) ^ (-(scale B / 2)) * (2 : ℝ) ^ (scale B / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  have hproduct : lowL B a * highU B a = z ^ 2 := by
    rw [hL, hU]
    calc
      _ = z ^ 2 * ((2 : ℝ) ^ (-(scale B / 2)) * (2 : ℝ) ^ (scale B / 2)) := by ring
      _ = z ^ 2 := by rw [hrecip, mul_one]
  have hsqrt : Real.sqrt (2 * lowL B a * highU B a) = z * Real.sqrt 2 := by
    have harg : 2 * lowL B a * highU B a = z ^ 2 * 2 := by nlinarith [hproduct]
    rw [harg, Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq hz.le]
  rw [hsqrt, hL, hU]
  have hscaled := mul_lt_mul_of_pos_left hlam hz
  nlinarith

#print axioms solution
