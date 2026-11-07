-- Prove2me | solution 1 for Matrix.affineLineDet_eval_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:23.983915+00:00
-- url     : https://prove2.me/submissions/dff7bb18-fb9b-49a2-9832-dc8d25731b50

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
    Polynomial.eval 1 (affineLineDet A) = Matrix.det A := by
  rw [eval_affineLineDet]
  congr 1
  module
end Matrix
