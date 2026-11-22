-- Prove2me | solution 1 for Lean4LPD.epsJump_mul_chainWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:25.887062+00:00
-- url     : https://prove2.me/submissions/bd4817d3-c368-447b-93b0-319753741768

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_chainWeight_nonneg
public import Theorems.Thm_Lean4LPD_epsJump_mul_chainWeight_eq_partFactor
public import Theorems.Thm_Lean4LPD_partFactor_le_of_one_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {j m : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    epsJump kh1 c a j m * chainWeight kh1 c a (m - j)
      ≤ (9 / 4 : ℝ) ^ (j - 1) * chainWeight kh1 c a m := by
  rw [epsJump_mul_chainWeight_eq_partFactor hc kh1 a hjm]
  apply mul_le_mul_of_nonneg_right _ (chainWeight_nonneg hkh hc ha m)
  apply partFactor_le_of_one_le hj
  exact (by exact_mod_cast hjm : (j : ℝ) ≤ m).trans (le_add_of_nonneg_right hc)
end Lean4LPD
