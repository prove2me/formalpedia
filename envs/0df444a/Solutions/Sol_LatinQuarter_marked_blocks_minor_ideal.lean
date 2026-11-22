-- Prove2me | solution 1 for LatinQuarter.marked_blocks_minor_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:49.709036+00:00
-- url     : https://prove2.me/submissions/ead2d9a5-1ba7-47c3-acc0-745757bd072a

module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.CharP.Frobenius
public import Definitions.Def_LeanPool_LatinQuarter_Minors
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Vanishing
public import Theorems.Thm_LatinQuarter_isUnit_det_of_square_map_eq_one
public import Theorems.Thm_LatinQuarter_allMinorsIn_fromBlocks_diagonal
public import Theorems.Thm_LatinQuarter_allMinorsIn_mul_left
public import Theorems.Thm_LatinQuarter_allMinorsIn_mul_right


set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R] [CharP R 2]
namespace LatinQuarter
theorem _root_.solution {k h : ℕ}
    (A : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin h) R)
    (C : Matrix (Fin h) (Fin k) R)
    (D : Matrix (Fin h) (Fin h) R)
    (hA : squareHom.mapMatrix A = 1)
    (hC : C.map squareHom = 0)
    (hD : D.map squareHom = 0) :
    ∃ z : Fin h × Fin h → R,
      (∀ j, z j * z j = 0) ∧
      ∀ t, AllMinorsIn (Matrix.fromBlocks A B C D) t
        (Ideal.span (Set.range z) ^ (t - k)) := by
  classical
  let := Matrix.invertibleOfIsUnitDet A (isUnit_det_of_square_map_eq_one A hA)
  let Z := D - C * ⅟A * B
  let z : Fin h × Fin h → R := fun p => Z p.1 p.2
  refine ⟨z, ?_, ?_⟩
  · have hm : squareHom.mapMatrix Z = 0 := by
      simp only [Z, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub squareHom),
        Matrix.map_mul]
      change D.map squareHom -
        C.map squareHom * squareHom.mapMatrix (⅟A) * B.map squareHom = 0
      rw [hC, hD, Matrix.zero_mul, Matrix.zero_mul, sub_zero]
    intro j
    have hj := congrArg (fun M => M j.1 j.2) hm
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, squareHom,
      frobenius_def, pow_two, Matrix.zero_apply] using hj
  · intro t
    rw [Matrix.fromBlocks_eq_of_invertible₁₁ A B C D]
    apply allMinorsIn_mul_right
    apply allMinorsIn_mul_left
    apply allMinorsIn_fromBlocks_diagonal
    intro i j
    exact Ideal.subset_span ⟨(i, j), rfl⟩
end LatinQuarter
