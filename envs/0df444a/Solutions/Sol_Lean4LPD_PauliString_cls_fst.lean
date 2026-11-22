-- Prove2me | solution 1 for Lean4LPD.PauliString.cls_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:20.245519+00:00
-- url     : https://prove2.me/submissions/faa5fe9c-779b-40fc-b545-e8160d5a8dcd

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
theorem _root_.solution (s : PauliString n) : (cls s).1 = s.x := rfl
end Lean4LPD.PauliString
