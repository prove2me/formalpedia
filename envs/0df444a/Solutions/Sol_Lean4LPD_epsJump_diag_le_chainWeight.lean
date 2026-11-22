-- Prove2me | solution 1 for Lean4LPD.epsJump_diag_le_chainWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:06.295139+00:00
-- url     : https://prove2.me/submissions/cbea6c72-4762-4b12-a9af-0921f22fb5e4

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_chainWeight_zero
public import Theorems.Thm_Lean4LPD_epsJump_mul_chainWeight_le
attribute [local simp] Lean4LPD.chainWeight_zero

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    epsJump kh1 c a m m ≤ (9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m := by
  simpa using epsJump_mul_chainWeight_le hkh hc ha hm (le_refl m)
end Lean4LPD
