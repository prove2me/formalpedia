-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:24.721687+00:00
-- url     : https://prove2.me/submissions/2ffbb1a9-59ce-4b2f-817d-0bc93a6a4774

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul
public import Theorems.Thm_Lean4LPD_PauliString_commute_iff_sympForm_eq_zero


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : sympForm s t = 0) :
    Commute (toMatrix s) (toMatrix t) := by
  rw [Commute, SemiconjBy, toMatrix_mul, toMatrix_mul,
    ((commute_iff_sympForm_eq_zero s t).2 h).eq]
end Lean4LPD.PauliString
