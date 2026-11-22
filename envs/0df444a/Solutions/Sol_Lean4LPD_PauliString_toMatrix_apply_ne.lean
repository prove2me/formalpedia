-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:07:41.837808+00:00
-- url     : https://prove2.me/submissions/49bd1b57-a751-46de-bffc-23f6da9074a4

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
theorem _root_.solution (s : PauliString n) {a b : Bits n} (h : a ≠ b + s.x) :
    toMatrix s a b = 0 := by rw [toMatrix_apply, if_neg h]
end Lean4LPD.PauliString
