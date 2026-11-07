-- Prove2me | solution 1 for Matrix.affineLineDet_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:11.03475+00:00
-- url     : https://prove2.me/submissions/16a077ae-312b-47a6-888b-8c4b2dd0508b

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Theorems.Thm_Matrix_eval_affineLineDet

set_option autoImplicit false
open scoped Matrix
open Matrix
open scoped Polynomial
namespace Matrix
theorem _root_.solution
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    (affineLineDet A).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_affineLineDet]
  rw [zero_smul, add_zero, Matrix.det_one]
end Matrix
