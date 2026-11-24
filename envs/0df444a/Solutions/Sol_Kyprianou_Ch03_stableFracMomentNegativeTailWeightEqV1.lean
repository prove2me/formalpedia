-- Prove2me | solution 1 for Kyprianou.Ch03.stableFracMomentNegativeTailWeightEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:42:37.248441+00:00
-- url     : https://prove2.me/submissions/635fb7a3-dd09-4a2b-8dff-d5152b3d7a82

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (alpha cPlus cMinus eta x : Real) (hCMinus : 0 ≤ cMinus) (hx : x ≤ -1) :
    ((Real.toNNReal (if 0 < x then cPlus / (x ^ (1 + alpha))
       else if x < 0 then cMinus / ((-x) ^ (1 + alpha)) else 0) : NNReal) : Real) *
      (max |x| 1) ^ eta = cMinus * (-x) ^ (eta - 1 - alpha) := by
  have hx' : x < 0 := by linarith
  have h1 : 1 ≤ -x := by linarith
  rw [if_neg (not_lt.mpr hx'.le), if_pos hx']
  rw [Real.coe_toNNReal _ (by positivity), abs_of_neg hx', max_eq_left h1]
  calc
    _ = cMinus * ((-x)^eta / (-x)^(1+alpha)) := by ring
    _ = _ := by rw [← Real.rpow_sub (by linarith : 0 < -x)]; congr 2 <;> ring
