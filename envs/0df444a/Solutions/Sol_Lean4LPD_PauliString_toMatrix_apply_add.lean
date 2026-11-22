-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_apply_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:07:08.4038+00:00
-- url     : https://prove2.me/submissions/485a3d53-ef89-457e-b35f-1b034a9d0a64

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s : PauliString n) (b : Bits n) :
    toMatrix s (b + s.x) b = iPow s.phase * negOnePow (s.z ⬝ᵥ b) := by
  rw [toMatrix_apply, if_pos rfl]
end Lean4LPD.PauliString
