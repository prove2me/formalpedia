-- Prove2me | solution 1 for LatinQuarter.shifted_tags_product_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:15.737728+00:00
-- url     : https://prove2.me/submissions/a5fbdf3c-a999-4c9d-bea5-17deb38fb6bd

module
public import Definitions.Def_LeanPool_LatinQuarter_Vanishing
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_Shifted
public import Theorems.Thm_LatinQuarter_shiftedTags_square
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
public import Theorems.Thm_LatinQuarter_marked_blocks_product_vanishes
public import Theorems.Thm_LatinQuarter_tag_sq
attribute [local simp] LatinQuarter.allTagsExponent_apply
attribute [local simp] LatinQuarter.allTagsExponent_support
attribute [local simp] LatinQuarter.tag_sq



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
namespace LatinQuarter
theorem _root_.solution {N ι : Type*} [Fintype ι]
    {k h : ℕ} (e : Fin k ⊕ Fin h ≃ N)
    (α : ι → Type*) [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (r c : (i : ι) → α i → N)
    (hbudget : h * h < ∑ i, (Fintype.card (α i) - k)) :
    (∏ i, ((shiftedTags e).submatrix (r i) (c i)).det) = 0 := by
  classical
  let M := (shiftedTags e).submatrix e e
  let A := M.submatrix Sum.inl Sum.inl
  let B := M.submatrix Sum.inl Sum.inr
  let C := M.submatrix Sum.inr Sum.inl
  let D := M.submatrix Sum.inr Sum.inr
  have hA : squareHom.mapMatrix A = 1 := by
    ext i j
    change squareHom (shiftedTags e (e (Sum.inl i)) (e (Sum.inl j))) = _
    rw [shiftedTags_square]
    simp [markedConstant, Matrix.one_apply, e.injective.eq_iff]
  have hC : C.map squareHom = 0 := by
    ext i j
    change squareHom (shiftedTags e (e (Sum.inr i)) (e (Sum.inl j))) = _
    rw [shiftedTags_square]
    simp [markedConstant]
  have hD : D.map squareHom = 0 := by
    ext i j
    change squareHom (shiftedTags e (e (Sum.inr i)) (e (Sum.inr j))) = _
    rw [shiftedTags_square]
    simp [markedConstant]
  let q (i : ι) := (Fintype.equivFin (α i)).symm
  have hv := marked_blocks_product_vanishes A B C D hA hC hD
    (fun i => Fintype.card (α i))
    (fun i j => e.symm (r i (q i j)))
    (fun i j => e.symm (c i (q i j))) hbudget
  have hM : Matrix.fromBlocks A B C D = M := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [hM] at hv
  have heq (i : ι) :
      (M.submatrix (fun j => e.symm (r i (q i j)))
        (fun j => e.symm (c i (q i j)))).det =
      ((shiftedTags e).submatrix (r i) (c i)).det := by
    have hm : M.submatrix (fun j => e.symm (r i (q i j)))
        (fun j => e.symm (c i (q i j))) =
        (((shiftedTags e).submatrix (r i) (c i)).submatrix (q i) (q i)) := by
      ext a b
      simp [M, Matrix.submatrix]
    rw [hm, Matrix.det_submatrix_equiv_self]
  simp_rw [heq] at hv
  exact hv
end LatinQuarter
