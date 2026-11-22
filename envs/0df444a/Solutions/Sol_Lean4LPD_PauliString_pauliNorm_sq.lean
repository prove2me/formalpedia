-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:23.914955+00:00
-- url     : https://prove2.me/submissions/311c7c5a-2bd5-47c8-97d4-99d324608f8d

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_pauliNormSq_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm O ^ 2 = pauliNormSq O := Real.sq_sqrt (pauliNormSq_nonneg O)
end Lean4LPD.PauliString
