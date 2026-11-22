-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.discardedStep_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:51:24.28745+00:00
-- url     : https://prove2.me/submissions/e37fff0b-8860-49d4-a8bf-22dac6339765

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_traj_two
public import Theorems.Thm_Lean4LPD_DiscardWitness_step_one
public import Theorems.Thm_Lean4LPD_PauliString_trotterStepTraj_zero
attribute [local simp] Lean4LPD.PauliString.trotterStepTraj_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : discardedStep Gs angles 2 1 (toMatrix P) 0 = toMatrix Q := by
  rw [discardedStep, trotterStepTraj_zero, step_one, traj_two, sub_zero]
end Lean4LPD.DiscardWitness
