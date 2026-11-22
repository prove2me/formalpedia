-- Prove2me | solution 1 for Lean4LPD.PauliString.diag_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:14.115159+00:00
-- url     : https://prove2.me/submissions/0f28178a-55cc-417e-96ea-0190d909f22c

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (u : PauliString n) (a : Bits n) :
    a = a + u.x ↔ u.x = 0 := by
  constructor
  · intro h
    have h' : a + 0 = a + u.x := by rwa [add_zero]
    exact (add_left_cancel h').symm
  · intro h; rw [h, add_zero]
end Lean4LPD.PauliString
