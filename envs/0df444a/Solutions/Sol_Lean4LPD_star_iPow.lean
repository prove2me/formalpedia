-- Prove2me | solution 1 for Lean4LPD.star_iPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:06.511372+00:00
-- url     : https://prove2.me/submissions/946dd097-f217-4698-aebf-edae8d0ced9b

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_conj_iPow

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
namespace Lean4LPD
theorem _root_.solution (k : ZMod 4) : star (iPow k) = iPow (-k) := by
  rw [Complex.star_def]; exact conj_iPow k
end Lean4LPD
