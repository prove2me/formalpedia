-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.second_rotation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:54.065822+00:00
-- url     : https://prove2.me/submissions/fae6b00b-f7d2-4ed8-99b6-87cf2b4d793d

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_isSelfAdjoint_Q
public import Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch_commute


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution (θ : ℝ) :
    rot (toMatrix Q) θ * toMatrix Q * rot (toMatrix Q) (-θ) = toMatrix Q :=
  pauli_rotation_branch_commute isSelfAdjoint_Q (by decide) θ
end Lean4LPD.DiscardWitness
