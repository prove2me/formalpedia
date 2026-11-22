-- Prove2me | solution 1 for Lean4LPD.cZero_le_two_of_gamma_le_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:45.040626+00:00
-- url     : https://prove2.me/submissions/cd117ac7-6356-4b03-aa08-7f470dd200b5

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Theorems.Thm_Lean4LPD_cZero_le_two
public import Theorems.Thm_Lean4LPD_le_r_of_gamma_le_six

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hG6 : G ≤ 6) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 :=
  cZero_le_two h hm1 (le_r_of_gamma_le_six h hm1 hG6) hB0 hB1
end Lean4LPD
