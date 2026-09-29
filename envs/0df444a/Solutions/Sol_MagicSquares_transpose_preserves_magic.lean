-- Prove2me | solution 1 for MagicSquares.transpose_preserves_magic
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:16:27.501728+00:00
-- url     : https://prove2.me/submissions/1dd450ee-ce18-4a56-a7a9-8d76aec14f9f

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-! Auxiliary line-sum identities for the symmetry operations. The published
definition module provides only the operations, so the reindexing facts are
recorded here. -/

section helpers
variable {n : ℕ} {α : Type*} [AddCommMonoid α]

private lemma rowSum_transpose' (M : Square n α) (i : Fin n) :
    rowSum (transpose M) i = colSum M i := by
  simp [rowSum, colSum, transpose]

private lemma colSum_transpose' (M : Square n α) (j : Fin n) :
    colSum (transpose M) j = rowSum M j := by
  simp [rowSum, colSum, transpose]

private lemma diagSum_transpose' (M : Square n α) :
    diagSum (transpose M) = diagSum M := by
  simp [diagSum, transpose]

private lemma antiDiagSum_transpose' (M : Square n α) :
    antiDiagSum (transpose M) = antiDiagSum M := by
  simp only [antiDiagSum, transpose]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M (Fin.rev i) i)]
  simp

private lemma rowSum_flipVertical' (M : Square n α) (i : Fin n) :
    rowSum (flipVertical M) i = rowSum M (Fin.rev i) := by
  simp [rowSum, flipVertical]

private lemma colSum_flipVertical' (M : Square n α) (j : Fin n) :
    colSum (flipVertical M) j = colSum M j := by
  simp only [colSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i j)]

private lemma diagSum_flipVertical' (M : Square n α) :
    diagSum (flipVertical M) = antiDiagSum M := by
  simp only [diagSum, antiDiagSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i (Fin.rev i))]
  simp

private lemma antiDiagSum_flipVertical' (M : Square n α) :
    antiDiagSum (flipVertical M) = diagSum M := by
  simp only [antiDiagSum, diagSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i i)]

private lemma rowSum_flipHorizontal' (M : Square n α) (i : Fin n) :
    rowSum (flipHorizontal M) i = rowSum M i := by
  simp only [rowSum, flipHorizontal]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun j => M i j)]

private lemma colSum_flipHorizontal' (M : Square n α) (j : Fin n) :
    colSum (flipHorizontal M) j = colSum M (Fin.rev j) := by
  simp [colSum, flipHorizontal]

private lemma diagSum_flipHorizontal' (M : Square n α) :
    diagSum (flipHorizontal M) = antiDiagSum M := by
  simp only [diagSum, antiDiagSum, flipHorizontal]

private lemma antiDiagSum_flipHorizontal' (M : Square n α) :
    antiDiagSum (flipHorizontal M) = diagSum M := by
  simp [antiDiagSum, diagSum, flipHorizontal]

end helpers

/-- Rows and columns are exchanged; both diagonals are fixed. -/
theorem solution {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (transpose M) s := by
  constructor
  · constructor
    · intro i
      simpa [rowSum_transpose'] using hM.1.2 i
    · intro j
      simpa [colSum_transpose'] using hM.1.1 j
  · constructor
    · simpa [diagSum_transpose'] using hM.2.1
    · simpa [antiDiagSum_transpose'] using hM.2.2
