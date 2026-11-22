-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:29.14474+00:00
-- url     : https://prove2.me/submissions/4bb1e79b-00fb-4d2a-9a4d-0c81ad737fe2

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_iPow_ne_zero
public import Theorems.Thm_Lean4LPD_negOnePow_ne_zero
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_apply_add

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s : PauliString n) : toMatrix s ≠ 0 := by
  intro h
  have := congrFun (congrFun h (0 + s.x)) 0
  rw [toMatrix_apply_add] at this
  exact (mul_ne_zero (iPow_ne_zero _) (negOnePow_ne_zero _)) this
end Lean4LPD.PauliString
