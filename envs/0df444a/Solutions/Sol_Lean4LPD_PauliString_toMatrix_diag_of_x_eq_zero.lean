-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_diag_of_x_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:37.457544+00:00
-- url     : https://prove2.me/submissions/f50e11b7-eddc-47ec-bf42-5fe3a74f86e2

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
theorem _root_.solution (hu : u.x = 0) (a : Bits n) :
    toMatrix u a a = iPow u.phase * negOnePow (u.z ⬝ᵥ a) := by
  rw [toMatrix_apply, if_pos ((diag_ne_zero_iff u a).2 hu)]
end Lean4LPD.PauliString
