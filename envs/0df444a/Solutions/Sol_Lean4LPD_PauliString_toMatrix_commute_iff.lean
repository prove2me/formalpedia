-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_commute_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:26.279923+00:00
-- url     : https://prove2.me/submissions/68e3fd54-59e4-4a1a-974b-b1091362c4af

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_injective
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_commute
public import Theorems.Thm_Lean4LPD_PauliString_commute_iff_sympForm_eq_zero


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s t : PauliString n) :
    Commute (toMatrix s) (toMatrix t) ↔ sympForm s t = 0 := by
  refine ⟨fun h => ?_, toMatrix_commute⟩
  rw [← commute_iff_sympForm_eq_zero]
  exact toMatrix_injective (by rw [← toMatrix_mul, ← toMatrix_mul]; exact h.eq)
end Lean4LPD.PauliString
