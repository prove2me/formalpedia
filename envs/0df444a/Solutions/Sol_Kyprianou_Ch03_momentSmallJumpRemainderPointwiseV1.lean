-- Prove2me | solution 1 for Kyprianou.Ch03.momentSmallJumpRemainderPointwiseV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:45:03.252577+00:00
-- url     : https://prove2.me/submissions/2a339efa-d32e-438f-9d8e-786ba8a717ea

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (b x : Real) (hx : |x| ≤ 1) :
    ‖Real.exp (b * x) - 1 - b * x‖ ≤
      (Real.exp |b| + 1 + |b| + 1) * b ^ 2 * x ^ 2 := by
  let C : ℝ := Real.exp |b| + 1 + |b| + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith [Real.exp_pos |b|, abs_nonneg b]
  have hbx : |b * x| ≤ |b| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx (abs_nonneg b)
  have he : Real.exp (b * x) ≤ Real.exp |b| :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans hbx)
  have hnon : 0 ≤ Real.exp (b * x) - 1 - b * x := by linarith [Real.add_one_le_exp (b*x)]
  change ‖Real.exp (b*x)-1-b*x‖ ≤ C*b^2*x^2
  rw [Real.norm_eq_abs, abs_of_nonneg hnon]
  by_cases hs : |b*x| ≤ 1
  · have h := Real.abs_exp_sub_one_sub_id_le hs
    rw [abs_of_nonneg hnon] at h
    calc
      _ ≤ (b*x)^2 := h
      _ = b^2*x^2 := by ring
      _ ≤ C*b^2*x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg (sq_nonneg b) (sq_nonneg x))]
  · have hl : 1 ≤ (b*x)^2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (le_of_lt (lt_of_not_ge hs)) 2
      simpa only [one_pow, sq_abs] using h
    have hneg : -(b*x) ≤ |b| := (neg_le_abs _).trans hbx
    calc
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ C * (b*x)^2 := by nlinarith [mul_nonneg (show 0 ≤ C by linarith) (sub_nonneg.mpr hl)]
      _ = C*b^2*x^2 := by ring
