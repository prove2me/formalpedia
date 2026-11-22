-- Prove2me | solution 1 for LatinQuarter.allMinorsIn_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:09.754252+00:00
-- url     : https://prove2.me/submissions/34b53cb0-4ed2-42ad-8354-e89c83b219e1

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Operations
public import Definitions.Def_LeanPool_LatinQuarter_Minors
public import Theorems.Thm_LatinQuarter_allMinorsIn_mul_left
public import Theorems.Thm_LatinQuarter_allMinorsIn_transpose

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R]
namespace LatinQuarter
theorem _root_.solution {m n p : Type*} [Fintype n]
    (A : Matrix m n R) (B : Matrix n p R) {t : ℕ} {J : Ideal R}
    (hA : AllMinorsIn A t J) : AllMinorsIn (A * B) t J := by
  have h := allMinorsIn_mul_left B.transpose A.transpose (allMinorsIn_transpose A hA)
  have h' := allMinorsIn_transpose (B.transpose * A.transpose) h
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h'
end LatinQuarter
