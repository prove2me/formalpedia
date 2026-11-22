-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.interior_highNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:57.388895+00:00
-- url     : https://prove2.me/submissions/2ed37b98-0cbe-4ead-a8fa-a20b8b5cf2d7

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_Q_highNorm
public import Theorems.Thm_Lean4LPD_DiscardWitness_interior_eq_Q

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : highNorm 1 (trotterTraj Gs angles 2 1 (toMatrix P) 1) = 1 := by
  rw [interior_eq_Q, Q_highNorm]
end Lean4LPD.DiscardWitness
