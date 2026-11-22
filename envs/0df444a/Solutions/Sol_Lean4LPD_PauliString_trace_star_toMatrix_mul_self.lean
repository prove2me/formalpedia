-- Prove2me | solution 1 for Lean4LPD.PauliString.trace_star_toMatrix_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:48.593728+00:00
-- url     : https://prove2.me/submissions/1dccca2a-bad3-4c06-b11a-b12c7290403a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Theorems.Thm_Lean4LPD_PauliString_star_eq_inv
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_star
public import Theorems.Thm_Lean4LPD_card_bits
attribute [local simp] Lean4LPD.PauliString.toMatrix_one



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s : PauliString n) :
    (star (toMatrix s) * toMatrix s).trace = (2 : ℂ) ^ n := by
  rw [toMatrix_star, toMatrix_mul, star_eq_inv, inv_mul_cancel, toMatrix_one, Matrix.trace_one,
    card_bits]
  push_cast
  ring
end Lean4LPD.PauliString
