-- Prove2me | solution 2 for Kyprianou.Ch03.stableFracMomentNegativeTailWeightEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:48:35.658294+00:00
-- url     : https://prove2.me/submissions/5a461ffe-68ed-41a1-86d7-e11138eafa75

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (alpha cPlus cMinus eta x : Real) (hCMinus : 0 ≤ cMinus) (hx : x ≤ -1) :
    ((Real.toNNReal (if 0 < x then cPlus / (x ^ (1 + alpha))
       else if x < 0 then cMinus / ((-x) ^ (1 + alpha)) else 0) : NNReal) : Real) *
      (max |x| 1) ^ eta = cMinus * (-x) ^ (eta - 1 - alpha) := by
  have hx' : x < 0 := by linarith
  have hp : 0 < -x := by linarith
  have h1 : 1 ≤ -x := by linarith
  have hn : 0 ≤ cMinus / (-x) ^ (1 + alpha) := by positivity
  rw [if_neg (not_lt.mpr hx'.le), if_pos hx']
  rw [show ((cMinus / (-x) ^ (1 + alpha)).toNNReal : ℝ) =
    cMinus / (-x) ^ (1 + alpha) by simp [Real.coe_toNNReal, hn]]
  rw [abs_of_neg hx', max_eq_left h1]
  calc
    _ = cMinus * ((-x)^eta / (-x)^(1+alpha)) := by ring
    _ = _ := by rw [← Real.rpow_sub hp]; congr 2 <;> ring
