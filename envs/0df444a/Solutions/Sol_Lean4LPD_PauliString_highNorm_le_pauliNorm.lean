-- Prove2me | solution 1 for Lean4LPD.PauliString.highNorm_le_pauliNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:30.977293+00:00
-- url     : https://prove2.me/submissions/fbbc6c32-f1b3-4cc6-8ce4-b5a79ce65561

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_norm_coeffVec
public import Theorems.Thm_Lean4LPD_PauliString_norm_restr_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm w O ≤ pauliNorm O := by
  rw [highNorm, ← norm_coeffVec]
  exact norm_restr_le _ _
end Lean4LPD.PauliString
