-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_sub_truncOp_highSet_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:03.147836+00:00
-- url     : https://prove2.me/submissions/516d6f41-31a5-444f-8423-ba6eab534721

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Theorems.Thm_Lean4LPD_PauliString_sub_truncOp_compl
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_truncOp_highSet

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (O - truncOp (highSet n w)ᶜ O) = highNorm w O := by
  rw [sub_truncOp_compl, pauliNorm_truncOp_highSet]
end Lean4LPD.PauliString
