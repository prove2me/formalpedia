-- Prove2me | solution 1 for Matrix.map_affineLineDet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:28.393332+00:00
-- url     : https://prove2.me/submissions/49975e50-c018-44e1-9365-597f404bb148

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
    {R S n : Type*} [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
    (f : R →+* S) (A : Matrix n n R) :
    Polynomial.map f (affineLineDet A) = affineLineDet (A.map f) := by
  change Polynomial.mapRingHom f (Matrix.det
      ((1 : Matrix n n R[X]) + (Polynomial.X : R[X]) •
        (A.map (Polynomial.C : R →+* R[X]) - 1))) = _
  rw [RingHom.map_det]
  change Matrix.det ((Polynomial.mapRingHom f).mapMatrix
      ((1 : Matrix n n R[X]) + (Polynomial.X : R[X]) •
        (A.map (Polynomial.C : R →+* R[X]) - 1))) =
    Matrix.det ((1 : Matrix n n S[X]) + (Polynomial.X : S[X]) •
      ((A.map f).map (Polynomial.C : S →+* S[X]) - 1))
  apply congrArg (fun M : Matrix n n S[X] => Matrix.det M)
  apply Matrix.ext
  intro i j
  change Polynomial.map f
      ((if i = j then 1 else 0) + Polynomial.X *
        (Polynomial.C (A i j) - (if i = j then 1 else 0))) =
    (if i = j then 1 else 0) + Polynomial.X *
      (Polynomial.C (f (A i j)) - (if i = j then 1 else 0))
  by_cases hij : i = j <;> simp [hij]
end Matrix
