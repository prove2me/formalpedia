-- Prove2me | solution 1 for Lean4LPD.PauliString.star_toMatrix_of_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:36.24673+00:00
-- url     : https://prove2.me/submissions/4fca5b06-0660-459f-9a2c-1f2518cc3ea2

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_star

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : IsSelfAdjoint s) :
    star (toMatrix s) = toMatrix s := by rw [toMatrix_star, h]
end Lean4LPD.PauliString
