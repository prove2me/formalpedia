-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.discardedStep_pauliNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:51:04.082212+00:00
-- url     : https://prove2.me/submissions/148f5e8a-84e6-4b58-b14d-725bdbf10065

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_Q_highNorm
public import Theorems.Thm_Lean4LPD_DiscardWitness_traj_two
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_discardedStep
public import Theorems.Thm_Lean4LPD_PauliString_trotterStepTraj_zero
attribute [local simp] Lean4LPD.PauliString.trotterStepTraj_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : pauliNorm (discardedStep Gs angles 2 1 (toMatrix P) 0) = 1 := by
  rw [pauliNorm_discardedStep, trotterStepTraj_zero, traj_two, Q_highNorm]
end Lean4LPD.DiscardWitness
