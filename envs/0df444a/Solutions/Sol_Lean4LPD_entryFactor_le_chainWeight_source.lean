-- Prove2me | solution 1 for Lean4LPD.entryFactor_le_chainWeight_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:29.544243+00:00
-- url     : https://prove2.me/submissions/db1ac216-0227-4091-924b-71c13e1d14cd

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_chainWeight_nonneg
public import Theorems.Thm_Lean4LPD_entryFactor_le_chainWeight
public import Theorems.Thm_Lean4LPD_chain_entry_inflation_le_source

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    entryFactor kh1 c a m
      ≤ (1 + 4 * Real.exp 1 * betaOf kh1 c a)
        * (9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m := by
  refine (entryFactor_le_chainWeight hkh hc ha hb hm).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (chain_entry_inflation_le_source hkh hc ha) (by positivity))
    (chainWeight_nonneg hkh hc ha m)
end Lean4LPD
