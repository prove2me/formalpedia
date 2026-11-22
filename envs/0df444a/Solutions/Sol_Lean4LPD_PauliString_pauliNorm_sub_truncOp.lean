-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_sub_truncOp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:46.50762+00:00
-- url     : https://prove2.me/submissions/0221e0ce-558a-41b1-99e7-c0e29d4e1c95

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Theorems.Thm_Lean4LPD_PauliString_sub_truncOp
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_truncOp

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (S : Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (O - truncOp S O) = ‖restr Sᶜ (coeffVec O)‖ := by
  rw [sub_truncOp, pauliNorm_truncOp]
end Lean4LPD.PauliString
