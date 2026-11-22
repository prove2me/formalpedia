-- Prove2me | solution 1 for Lean4LPD.PauliString.cls_herm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:16:25.689853+00:00
-- url     : https://prove2.me/submissions/d99d000a-38c7-4e9a-b599-65815da1ea5a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (p : PauliIndex n) : cls (herm p) = p := rfl
end Lean4LPD.PauliString
