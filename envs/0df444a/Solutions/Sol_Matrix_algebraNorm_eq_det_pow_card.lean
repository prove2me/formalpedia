-- Prove2me | solution 1 for Matrix.algebraNorm_eq_det_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:42.604523+00:00
-- url     : https://prove2.me/submissions/dd4bc841-bb6e-4039-b274-8ce7bf3d7aea

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Theorems.Thm_Matrix_leftMulMatrix_stdBasis_eq_kronecker

set_option autoImplicit false
open scoped Matrix
open Matrix
open scoped Polynomial
namespace Matrix
theorem _root_.solution
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    Algebra.norm R A = Matrix.det A ^ Fintype.card n := by
  rw [Algebra.norm_eq_matrix_det (Matrix.stdBasis R n n),
    leftMulMatrix_stdBasis_eq_kronecker]
  change Matrix.det (Matrix.kroneckerMap (fun a b : R => a * b)
    A (1 : Matrix n n R)) = _
  rw [Matrix.det_kronecker]
  simp
end Matrix
