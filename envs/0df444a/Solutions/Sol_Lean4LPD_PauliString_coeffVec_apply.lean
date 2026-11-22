-- Prove2me | solution 1 for Lean4LPD.PauliString.coeffVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:16:31.999016+00:00
-- url     : https://prove2.me/submissions/9c77742c-3bd6-4e6b-b14e-e469639b2577

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
theorem _root_.solution (O : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) :
    (coeffVec O).ofLp p = coeff O p := rfl
end Lean4LPD.PauliString
