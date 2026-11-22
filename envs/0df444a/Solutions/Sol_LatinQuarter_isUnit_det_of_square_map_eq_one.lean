-- Prove2me | solution 1 for LatinQuarter.isUnit_det_of_square_map_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:37.684801+00:00
-- url     : https://prove2.me/submissions/21ecd7c7-53ff-4c9f-911a-305321c59c6b

module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.CharP.Frobenius
public import Definitions.Def_LeanPool_LatinQuarter_Minors
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Vanishing

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R] [CharP R 2]
namespace LatinQuarter
theorem _root_.solution {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R)
    (hA : squareHom.mapMatrix A = 1) : IsUnit A.det := by
  have hs : A.det * A.det = 1 := by
    have hm := squareHom.map_det A
    rw [hA, Matrix.det_one] at hm
    simpa only [squareHom, frobenius_def, pow_two] using hm
  exact ⟨⟨A.det, A.det, hs, hs⟩, rfl⟩
end LatinQuarter
