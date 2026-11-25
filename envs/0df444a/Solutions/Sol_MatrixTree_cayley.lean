-- Prove2me | solution 1 for MatrixTree.cayley
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:49:24.800697+00:00
-- url     : https://prove2.me/submissions/294333cd-1636-4fb1-96b7-2eece187e005

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_matrix_tree
public import Theorems.Thm_MatrixTree_det_complete_int
public import Theorems.Thm_MatrixTree_lapMatrix_top_apply

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by
  have h := matrix_tree (⊤ : SimpleGraph (Fin n)) ⟨0, hn⟩
  have hc : Nat.card {T : SimpleGraph (Fin n) // T.IsTree} =
      Nat.card {H : SimpleGraph (Fin n) // H ≤ ⊤ ∧ H.IsTree} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun H => by simp)
  have hcard : Fintype.card {u : Fin n // u ≠ ⟨0, hn⟩} = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  have hsub : ((⊤ : SimpleGraph (Fin n)).lapMatrix ℤ).submatrix
      (Subtype.val : {u // u ≠ (⟨0, hn⟩ : Fin n)} → Fin n) Subtype.val =
      Matrix.of fun i j => if i = j then (Fintype.card {u : Fin n // u ≠ ⟨0, hn⟩} : ℤ) else -1 := by
    ext i j
    simp only [submatrix_apply, lapMatrix_top_apply, of_apply, hcard, Nat.cast_sub hn,
      Nat.cast_one, Subtype.ext_iff]
  rw [hsub, det_complete_int, hcard] at h
  apply Nat.cast_injective (R := ℤ)
  rw [hc, h]
  push_cast [Nat.cast_sub hn]
  congr 1
  omega
end MatrixTree
