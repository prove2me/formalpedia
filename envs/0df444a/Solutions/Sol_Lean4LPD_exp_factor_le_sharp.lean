-- Prove2me | solution 1 for Lean4LPD.exp_factor_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:03:56.018314+00:00
-- url     : https://prove2.me/submissions/d07f8348-6788-4e84-b866-b90624c285ca

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
theorem _root_.solution {r m G : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) :
    exp (9 / 4 * (m + 1) / (r * G)) ≤ 1439 / 1250 := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := h
  have hrGpos : 0 < r * G := lt_of_lt_of_le (by nlinarith) hrG
  have hm2 : (2 : ℝ) ≤ m + 1 := by linarith
  have hkey : 9 / 4 * (m + 1) / (r * G) ≤ 9 / 64 := by
    rw [div_le_iff₀ hrGpos]
    nlinarith only [hrG, hm2]
  have hb := Real.exp_bound' (x := (9 : ℝ) / 64) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  calc exp (9 / 4 * (m + 1) / (r * G)) ≤ exp (9 / 64) := Real.exp_le_exp.mpr hkey
    _ ≤ _ := hb
    _ ≤ 1439 / 1250 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
end Lean4LPD
