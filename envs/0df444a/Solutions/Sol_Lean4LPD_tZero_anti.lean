-- Prove2me | solution 1 for Lean4LPD.tZero_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:30.818706+00:00
-- url     : https://prove2.me/submissions/e3d41f99-7be1-4caa-95ab-6e10210cad51

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {c c' G kh a : ℝ} (hc : 0 < c) (hcc : c ≤ c') (hG : 0 < G) (hkh : 1 < kh)
    (ha : 0 < a) : tZero c' G kh a ≤ tZero c G kh a := by
  have hpos : (0 : ℝ) < c * G * (kh - 1) * a := by
    have : (0 : ℝ) < kh - 1 := by linarith
    positivity
  have hpos' : (0 : ℝ) < c' * G * (kh - 1) * a := by
    have h1 : (0 : ℝ) < kh - 1 := by linarith
    have : (0 : ℝ) < c' := lt_of_lt_of_le hc hcc
    positivity
  unfold tZero
  apply one_div_le_one_div_of_le hpos
  have h1 : (0 : ℝ) < kh - 1 := by linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hG.le) h1.le) ha.le
end Lean4LPD
