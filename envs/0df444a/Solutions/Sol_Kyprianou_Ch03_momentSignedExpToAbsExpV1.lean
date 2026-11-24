-- Prove2me | solution 1 for Kyprianou.Ch03.momentSignedExpToAbsExpV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:51:38.333864+00:00
-- url     : https://prove2.me/submissions/6aa52f3b-f2b9-4b3d-931e-0f71ad8ed429

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (nu : Measure Real) (b : Real)
    (hp : Integrable (fun x : Real => Real.exp (b * x)) nu)
    (hm : Integrable (fun x : Real => Real.exp (-b * x)) nu) :
    Integrable (fun x : Real => Real.exp (b * |x|)) nu := by
  have h := hp.add hm
  apply h.mono (by fun_prop)
  filter_upwards [] with x
  have hpos := (Real.exp_pos (b * x)).le
  have hneg := (Real.exp_pos (-b * x)).le
  change ‖Real.exp (b * |x|)‖ ≤ ‖Real.exp (b * x) + Real.exp (-b * x)‖
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      Real.norm_eq_abs, abs_of_nonneg (add_nonneg hpos hneg)]
    exact le_add_of_nonneg_right hneg
  · rw [abs_of_neg (lt_of_not_ge hx), mul_neg, ← neg_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg hpos hneg)]
    exact le_add_of_nonneg_left hpos
