-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_diag_of_x_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:36.674027+00:00
-- url     : https://prove2.me/submissions/d5f0f661-de19-485c-8ba7-17d5f9479d7d

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Theorems.Thm_Lean4LPD_PauliString_diag_ne_zero_iff

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (hu : u.x ≠ 0) (a : Bits n) : toMatrix u a a = 0 := by
  rw [toMatrix_apply, if_neg]
  intro h
  exact hu ((diag_ne_zero_iff u a).1 h)
end Lean4LPD.PauliString
