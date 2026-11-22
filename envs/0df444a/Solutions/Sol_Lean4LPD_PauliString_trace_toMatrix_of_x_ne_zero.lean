-- Prove2me | solution 1 for Lean4LPD.PauliString.trace_toMatrix_of_x_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:16.725204+00:00
-- url     : https://prove2.me/submissions/92c6e8e2-ee5e-4c7c-ad7d-de4dc4400785

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_diag_of_x_ne_zero

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (hu : u.x ≠ 0) : (toMatrix u).trace = 0 := by
  rw [Matrix.trace]
  exact Finset.sum_eq_zero fun a _ => toMatrix_diag_of_x_ne_zero hu a
end Lean4LPD.PauliString
