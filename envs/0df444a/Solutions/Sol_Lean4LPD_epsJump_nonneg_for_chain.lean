-- Prove2me | solution 1 for Lean4LPD.epsJump_nonneg_for_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:00:26.900302+00:00
-- url     : https://prove2.me/submissions/5d93847b-9f61-4f18-b34a-9703433cd4d8

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_chainWeight_zero
public import Theorems.Thm_Lean4LPD_epsJump_nonneg

attribute [local simp] Lean4LPD.chainWeight_zero

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (j m : ℕ) :
    0 ≤ epsJump kh1 c a j m := by
  by_cases h : 1 ≤ m + j
  · exact epsJump_nonneg hkh hc ha j m h
  · have hm : m = 0 := by omega
    have hj : j = 0 := by omega
    subst m
    subst j
    simp [epsJump]
end Lean4LPD
