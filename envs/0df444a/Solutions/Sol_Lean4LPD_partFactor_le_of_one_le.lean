-- Prove2me | solution 1 for Lean4LPD.partFactor_le_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:31.919501+00:00
-- url     : https://prove2.me/submissions/914d8a20-645e-4fc0-9d58-aba3028f943f

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_partFactor_one
public import Theorems.Thm_Lean4LPD_partFactor_le


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {j : ℕ} {s : ℝ} (hj : 1 ≤ j) (hs : (j : ℝ) ≤ s) :
    partFactor j s ≤ (9 / 4 : ℝ) ^ (j - 1) := by
  by_cases hj1 : j = 1
  · subst j
    rw [partFactor_one (by norm_num at hs; linarith)]
    norm_num
  · exact partFactor_le (by omega) hs
end Lean4LPD
