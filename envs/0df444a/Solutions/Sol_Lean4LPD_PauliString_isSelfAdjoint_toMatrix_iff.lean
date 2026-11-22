-- Prove2me | solution 1 for Lean4LPD.PauliString.isSelfAdjoint_toMatrix_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:27.8255+00:00
-- url     : https://prove2.me/submissions/52faa678-851d-4d36-80a6-82e63ba636ad

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_star
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_injective
public import Theorems.Thm_Lean4LPD_PauliString_star_toMatrix_of_isSelfAdjoint

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution {s : PauliString n} :
    IsSelfAdjoint (toMatrix s) ↔ IsSelfAdjoint s := by
  constructor
  · intro h
    exact toMatrix_injective (by rw [← toMatrix_star]; exact h)
  · intro h
    exact star_toMatrix_of_isSelfAdjoint h
end Lean4LPD.PauliString
