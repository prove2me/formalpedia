-- Prove2me | solution 1 for MatrixTree.det_complete_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:19:06.263634+00:00
-- url     : https://prove2.me/submissions/8c76c188-a7d9-44f9-b936-bd4a218f0568

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_det_complete_rat

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (Matrix.of fun i j : ι => if i = j then (Fintype.card ι : ℤ) else -1).det =
      ((Fintype.card ι : ℤ) + 1) ^ (Fintype.card ι - 1) := by
  have h := (Int.castRingHom ℚ).map_det
    (Matrix.of fun i j : ι => if i = j then (Fintype.card ι : ℤ) else -1)
  have h2 : (Int.castRingHom ℚ).mapMatrix
      (Matrix.of fun i j : ι => if i = j then (Fintype.card ι : ℤ) else -1) =
      Matrix.of fun i j : ι => if i = j then (Fintype.card ι : ℚ) else -1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, map_apply, of_apply]
    split_ifs <;> simp
  rw [h2, det_complete_rat] at h
  apply Int.cast_injective (α := ℚ)
  rw [← eq_intCast (Int.castRingHom ℚ), h]
  push_cast
  rfl
end MatrixTree
