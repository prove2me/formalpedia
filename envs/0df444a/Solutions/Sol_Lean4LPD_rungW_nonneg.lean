-- Prove2me | solution 1 for Lean4LPD.rungW_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:17.669803+00:00
-- url     : https://prove2.me/submissions/b2dbf2da-10d9-45fb-b8f3-9298db2762da

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ rungW kh1 c m := by
  have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  unfold rungW
  have : (0 : ℝ) ≤ (m : ℝ) - 1 + c := by linarith
  positivity
end Lean4LPD
