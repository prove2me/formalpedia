-- Prove2me | solution 1 for Lean4LPD.PauliString.coeff_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:37.203707+00:00
-- url     : https://prove2.me/submissions/721fde84-2ff7-4be1-8332-218bd68c1437

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (A B : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) :
    coeff (A + B) p = coeff A p + coeff B p := by
  rw [coeff, coeff, coeff, Matrix.mul_add, Matrix.trace_add, mul_add]
end Lean4LPD.PauliString
