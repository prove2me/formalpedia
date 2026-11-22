-- Prove2me | solution 1 for Lean4LPD.PauliString.highNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:41.139805+00:00
-- url     : https://prove2.me/submissions/8355559e-b0ce-4f01-8fc8-6498f93cb190

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
theorem _root_.solution (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : 0 ≤ highNorm w O :=
  norm_nonneg _
end Lean4LPD.PauliString
