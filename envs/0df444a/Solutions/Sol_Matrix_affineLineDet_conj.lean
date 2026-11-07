-- Prove2me | solution 1 for Matrix.affineLineDet_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:35.648381+00:00
-- url     : https://prove2.me/submissions/f0e0fb33-619e-497b-8c1d-7a1bc320a59e

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
    (A Z Zi : Matrix n n R) (hZZi : Z * Zi = 1) :
    affineLineDet (Z * A * Zi) = affineLineDet A := by
  let c : R →+* R[X] := Polynomial.C
  let Ap := A.map c
  let Zp := Z.map c
  let Zip := Zi.map c
  have hZZip : Zp * Zip = 1 := by
    change (Z.map c) * (Zi.map c) = 1
    rw [← Matrix.map_mul, hZZi, Matrix.map_one] <;>
      first | exact map_zero c | exact map_one c
  have hmap : (Z * A * Zi).map c = Zp * Ap * Zip := by
    change (Z * A * Zi).map c = (Z.map c) * (A.map c) * (Zi.map c)
    rw [Matrix.map_mul, Matrix.map_mul] <;> exact map_zero c
  have hmatrix :
      (1 : Matrix n n R[X]) + (Polynomial.X : R[X]) •
          ((Z * A * Zi).map c - 1) =
        Zp * ((1 : Matrix n n R[X]) +
          (Polynomial.X : R[X]) • (Ap - 1)) * Zip := by
    rw [hmap]
    calc
      1 + (Polynomial.X : R[X]) • (Zp * Ap * Zip - 1) =
          Zp * Zip + (Polynomial.X : R[X]) •
            (Zp * Ap * Zip - Zp * Zip) := by rw [hZZip]
      _ = Zp * (1 + (Polynomial.X : R[X]) • (Ap - 1)) * Zip := by
        noncomm_ring
  rw [affineLineDet, affineLineDet, hmatrix,
    Matrix.det_mul, Matrix.det_mul]
  have hdet : Matrix.det Zp * Matrix.det Zip = 1 := by
    rw [← Matrix.det_mul, hZZip, Matrix.det_one]
  calc
    Matrix.det Zp * Matrix.det
          ((1 : Matrix n n R[X]) + (Polynomial.X : R[X]) • (Ap - 1)) *
        Matrix.det Zip =
      Matrix.det
          ((1 : Matrix n n R[X]) + (Polynomial.X : R[X]) • (Ap - 1)) *
        (Matrix.det Zp * Matrix.det Zip) := by ring
    _ = _ := by rw [hdet, mul_one]
end Matrix
