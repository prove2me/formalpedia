-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.boundary_highNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:59.770912+00:00
-- url     : https://prove2.me/submissions/22fc49c1-73b4-470f-bae1-dd6f4d6a79c9

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_trotterStepTraj_succ
public import Theorems.Thm_Lean4LPD_PauliString_trotterTraj_at_boundary


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : highNorm 1 (trotterTraj Gs angles 2 1 (toMatrix P) 2) = 0 := by
  have hb := trotterTraj_at_boundary Gs angles 2 1 (toMatrix P) 1 (by norm_num)
  rw [Nat.one_mul] at hb
  rw [hb]
  exact highNorm_trotterStepTraj_succ Gs angles 2 1 (toMatrix P) 0
end Lean4LPD.DiscardWitness
