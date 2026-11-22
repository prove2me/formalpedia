-- Prove2me | solution 1 for LatinQuarter.allMinorsIn_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:31.896294+00:00
-- url     : https://prove2.me/submissions/c0eaf235-9c3c-4899-9417-7dbb430c098b

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Operations
public import Definitions.Def_LeanPool_LatinQuarter_Minors

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R]
namespace LatinQuarter
theorem _root_.solution {m n : Type*} (M : Matrix m n R)
    {t : ℕ} {J : Ideal R} (hM : AllMinorsIn M t J) :
    AllMinorsIn M.transpose t J := by
  intro r c
  simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using hM c r
end LatinQuarter
