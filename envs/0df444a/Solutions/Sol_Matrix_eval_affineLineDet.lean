-- Prove2me | solution 1 for Matrix.eval_affineLineDet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:54:48.931049+00:00
-- url     : https://prove2.me/submissions/5cecdbf4-4f8b-4c08-86a4-0b06c4c00d0c

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
    (A : Matrix n n R) (a : R) :
    Polynomial.eval a (affineLineDet A) =
      Matrix.det ((1 : Matrix n n R) + a • (A - 1)) := by
  rw [affineLineDet]
  change Polynomial.evalRingHom a
    (Matrix.det ((1 : Matrix n n R[X]) +
      (Polynomial.X : R[X]) •
        (A.map (Polynomial.C : R →+* R[X]) - 1))) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change Polynomial.eval a
      ((if i = j then 1 else 0) + Polynomial.X *
        (Polynomial.C (A i j) - (if i = j then 1 else 0))) =
    (if i = j then 1 else 0) + a *
      (A i j - (if i = j then 1 else 0))
  by_cases hij : i = j <;> simp [hij] <;> ring
end Matrix
