-- Prove2me | solution 1 for LatinQuarter.allMinorsIn_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:48.132175+00:00
-- url     : https://prove2.me/submissions/3d2c562d-41fd-4de9-86c3-3fa3b0f95541

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
theorem _root_.solution {m n p : Type*} [Fintype n]
    (A : Matrix m n R) (B : Matrix n p R) {t : ℕ} {J : Ideal R}
    (hB : AllMinorsIn B t J) : AllMinorsIn (A * B) t J := by
  classical
  intro r c
  have heq : (A * B).submatrix r c =
      fun i => ∑ j, A (r i) j • (fun l => B j (c l)) := by
    ext i l
    simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  change Matrix.detRowAlternating.toMultilinearMap
    (fun i => ∑ j, A (r i) j • (fun l => B j (c l))) ∈ J
  rw [MultilinearMap.map_sum]
  apply Submodule.sum_mem
  intro f _
  rw [MultilinearMap.map_smul_univ]
  exact J.smul_mem _ (hB f c)
end LatinQuarter
