-- Prove2me | solution 1 for Lean4LPD.PauliString.trace_star_toMatrix_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:39.028335+00:00
-- url     : https://prove2.me/submissions/e455b5b0-7f7a-4a98-ada0-d111ffe5cec6

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Theorems.Thm_Lean4LPD_PauliString_trace_star_toMatrix_mul

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : ¬(s.x = t.x ∧ s.z = t.z)) :
    (star (toMatrix s) * toMatrix t).trace = 0 := by
  rw [trace_star_toMatrix_mul, if_neg h]
end Lean4LPD.PauliString
