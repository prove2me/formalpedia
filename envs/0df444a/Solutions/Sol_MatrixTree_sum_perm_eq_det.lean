-- Prove2me | solution 1 for MatrixTree.sum_perm_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:06:58.213075+00:00
-- url     : https://prove2.me/submissions/8de58465-a39c-40e4-abab-38ef0ea76078

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) (e : Fin m → Fin k) :
    ∑ τ : Equiv.Perm (Fin m), (A.submatrix id (e ∘ τ)).det * ∏ i, B (e (τ i)) i =
      (A.submatrix id e).det * (B.submatrix e id).det := by
  have h : ∀ τ : Equiv.Perm (Fin m), A.submatrix id (e ∘ τ) = (A.submatrix id e).submatrix id τ :=
    fun τ => rfl
  simp only [h, det_permute', det_apply' (B.submatrix e id), mul_sum, submatrix_apply, id]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring
end MatrixTree
