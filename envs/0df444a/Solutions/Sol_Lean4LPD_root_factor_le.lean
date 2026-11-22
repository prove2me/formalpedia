-- Prove2me | solution 1 for Lean4LPD.root_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:45.574804+00:00
-- url     : https://prove2.me/submissions/32c1f383-aaec-4728-b3bf-f20e8597d3cd

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
theorem _root_.solution {m B : ℝ} (hm : 1 ≤ m) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ Real.sqrt 2 := by
  have hbase : (1 : ℝ) ≤ 1 + B := by linarith
  have hexp : (1 : ℝ) / (m + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h1 : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ (1 + B) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have h2 : (1 + B) ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h3 : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
  rw [← h3]
  linarith
end Lean4LPD
