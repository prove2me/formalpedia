-- Prove2me | solution 1 for Lean4LPD.PauliString.cls_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:43.444839+00:00
-- url     : https://prove2.me/submissions/f824efc8-07fc-4b6d-9959-74bf4c88d571

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
theorem _root_.solution (s : PauliString n) : (cls s).2 = s.z := rfl
end Lean4LPD.PauliString
