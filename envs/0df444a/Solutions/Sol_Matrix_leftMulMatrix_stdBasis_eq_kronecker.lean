-- Prove2me | solution 1 for Matrix.leftMulMatrix_stdBasis_eq_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:46:59.255667+00:00
-- url     : https://prove2.me/submissions/4ee2fcd7-b8a3-4faa-9b9d-8d20948b3af8

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm

set_option autoImplicit false
open scoped Matrix
open Matrix
open scoped Polynomial
namespace Matrix
theorem _root_.solution
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    Algebra.leftMulMatrix (Matrix.stdBasis R n n) A =
      Matrix.kronecker A (1 : Matrix n n R) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (A * Matrix.stdBasis R n n (k, l)) i j = _
  rw [Matrix.stdBasis_eq_single]
  by_cases hjl : j = l
  · subst l
    simp
  ·
    rw [Matrix.mul_single_apply_of_ne (hbj := hjl)]
    simp [hjl]
end Matrix
