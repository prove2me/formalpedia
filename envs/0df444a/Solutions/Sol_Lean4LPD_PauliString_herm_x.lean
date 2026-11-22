-- Prove2me | solution 1 for Lean4LPD.PauliString.herm_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:39.506166+00:00
-- url     : https://prove2.me/submissions/c1116636-1bb9-4b0d-8af9-55752c2d7aac

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
theorem _root_.solution (p : PauliIndex n) : (herm p).x = p.1 := rfl
end Lean4LPD.PauliString
