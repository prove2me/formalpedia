-- Prove2me | solution 1 for Lean4LPD.PauliString.trace_toMatrix_of_x_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:18.828843+00:00
-- url     : https://prove2.me/submissions/d2e74752-e426-4625-8570-9b9ed7f81f0e

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_diag_of_x_eq_zero

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (hu : u.x = 0) :
    (toMatrix u).trace = iPow u.phase * ∑ b : Bits n, negOnePow (u.z ⬝ᵥ b) := by
  rw [Matrix.trace, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Matrix.diag_apply, toMatrix_diag_of_x_eq_zero hu a]
end Lean4LPD.PauliString
