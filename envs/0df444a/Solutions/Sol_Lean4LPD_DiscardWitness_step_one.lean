-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.step_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:55.525384+00:00
-- url     : https://prove2.me/submissions/61c71d9d-ff52-4d56-837f-c0ba6acac5fd

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_cutoff_Q
public import Theorems.Thm_Lean4LPD_DiscardWitness_traj_two
public import Theorems.Thm_Lean4LPD_PauliString_trotterStepTraj_succ
public import Theorems.Thm_Lean4LPD_PauliString_trotterStepTraj_zero
attribute [local simp] Lean4LPD.PauliString.trotterStepTraj_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : trotterStepTraj Gs angles 2 1 (toMatrix P) 1 = 0 := by
  rw [trotterStepTraj_succ, trotterStepTraj_zero, traj_two, cutoff_Q]
end Lean4LPD.DiscardWitness
