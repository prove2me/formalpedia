-- Prove2me | solution 1 for Lean4LPD.cZero_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:19.658719+00:00
-- url     : https://prove2.me/submissions/995b1527-c9d7-4d75-ba44-03ecf004a3c2

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Theorems.Thm_Lean4LPD_cZero_le_two_sharp

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by
  have hs : Real.sqrt 2 ≤ 1.4143 := by
    have h2 : Real.sqrt 2 ≤ Real.sqrt (1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h2
  have := cZero_le_two_sharp h hm1 hr5 hB0 hB1
  nlinarith only [this, hs, Real.sqrt_nonneg 2]
end Lean4LPD
