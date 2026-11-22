-- Prove2me | solution 1 for Lean4LPD.iPow_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:16.889412+00:00
-- url     : https://prove2.me/submissions/b316c17c-96b3-42e1-a811-ac30b68b0bea

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_iPow_add
public import Theorems.Thm_Lean4LPD_iPow_eq_one_iff

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
namespace Lean4LPD
theorem _root_.solution : Function.Injective iPow := by
  intro k l h
  have hkl : iPow (k - l) = 1 := by
    rw [sub_eq_add_neg, iPow_add, h, ← iPow_add, add_neg_cancel, iPow_zero]
  exact sub_eq_zero.1 (iPow_eq_one_iff.1 hkl)
end Lean4LPD
