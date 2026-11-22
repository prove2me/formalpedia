-- Prove2me | solution 1 for Lean4LPD.PauliString.coeffVec_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:21.691703+00:00
-- url     : https://prove2.me/submissions/b0cc3717-4b2e-4946-8e53-ace4e0f3246b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Theorems.Thm_Lean4LPD_PauliString_coeff_sub

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (A B : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (A - B) = coeffVec A - coeffVec B := by
  ext p
  change coeff (A - B) p = coeff A p - coeff B p
  exact coeff_sub A B p
end Lean4LPD.PauliString
