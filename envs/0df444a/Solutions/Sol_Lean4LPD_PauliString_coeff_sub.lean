-- Prove2me | solution 1 for Lean4LPD.PauliString.coeff_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:01.113941+00:00
-- url     : https://prove2.me/submissions/5acc5610-9322-4fe6-9132-384a536eb025

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (A B : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) :
    coeff (A - B) p = coeff A p - coeff B p := by
  rw [coeff, coeff, coeff, Matrix.mul_sub, Matrix.trace_sub, mul_sub]
end Lean4LPD.PauliString
