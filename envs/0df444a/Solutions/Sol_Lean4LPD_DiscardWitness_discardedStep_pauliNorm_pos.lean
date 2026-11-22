-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.discardedStep_pauliNorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:52:11.444885+00:00
-- url     : https://prove2.me/submissions/c2996d6c-16be-4568-a3a3-2643b9b8d4cc

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_discardedStep_pauliNorm

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution :
    0 < pauliNorm (discardedStep Gs angles 2 1 (toMatrix P) 0) := by
  rw [discardedStep_pauliNorm]
  norm_num
end Lean4LPD.DiscardWitness
