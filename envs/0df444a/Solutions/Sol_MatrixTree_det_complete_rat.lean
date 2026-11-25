-- Prove2me | solution 1 for MatrixTree.det_complete_rat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:11:59.92207+00:00
-- url     : https://prove2.me/submissions/86e44266-a189-4dc4-834e-98ac2bbaf674

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (Matrix.of fun i j : ι => if i = j then (Fintype.card ι : ℚ) else -1).det =
      ((Fintype.card ι : ℚ) + 1) ^ (Fintype.card ι - 1) := by
  set c := Fintype.card ι with hc
  have hN : (c : ℚ) + 1 ≠ 0 := by positivity
  have h : (Matrix.of fun i j : ι => if i = j then (c : ℚ) else -1) =
      ((c : ℚ) + 1) • (1 + replicateCol Unit (fun _ : ι => -1 / ((c : ℚ) + 1)) *
        replicateRow Unit (fun _ : ι => (1 : ℚ))) := by
    ext i j
    simp only [of_apply, Matrix.smul_apply, Matrix.add_apply, one_apply, mul_apply,
      replicateCol_apply, replicateRow_apply, Finset.univ_unique, Finset.sum_singleton,
      smul_eq_mul]
    split_ifs <;> field_simp <;> ring
  rw [h, det_smul, det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ, ← hc, nsmul_eq_mul]
  clear_value c
  rcases c with _ | d
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast at hN ⊢
    field_simp
    ring
end MatrixTree
