-- Prove2me | solution 1 for Lean4LPD.PauliString.restr_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:47.093648+00:00
-- url     : https://prove2.me/submissions/aab735e7-ae3f-41fb-add2-6758bfcf98d5

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
theorem _root_.solution (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n))
    (p : PauliIndex n) : (restr S y).ofLp p = if p ∈ S then y.ofLp p else 0 := rfl
end Lean4LPD.PauliString
