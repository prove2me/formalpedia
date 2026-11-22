-- Prove2me | solution 1 for Lean4LPD.PauliString.coeffVec_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:46:49.032818+00:00
-- url     : https://prove2.me/submissions/84b85b41-a312-4ae8-91dd-5e4ca4a8e6e9

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Theorems.Thm_Lean4LPD_PauliString_coeff_add

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (A B : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (A + B) = coeffVec A + coeffVec B := by
  ext p
  change coeff (A + B) p = coeff A p + coeff B p
  exact coeff_add A B p
end Lean4LPD.PauliString
