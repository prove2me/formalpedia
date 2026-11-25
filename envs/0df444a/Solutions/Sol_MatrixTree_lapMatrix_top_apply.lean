-- Prove2me | solution 1 for MatrixTree.lapMatrix_top_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:12:32.348842+00:00
-- url     : https://prove2.me/submissions/e023b04e-2363-40e5-938c-9ff763f96714

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution (n : ℕ) (x y : Fin n) :
    (⊤ : SimpleGraph (Fin n)).lapMatrix ℤ x y = if x = y then ((n : ℤ) - 1) else -1 := by
  have := x.pos
  have hdeg : (⊤ : SimpleGraph (Fin n)).degree x = n - 1 := by
    rw [SimpleGraph.degree, show (⊤ : SimpleGraph (Fin n)).neighborFinset x = Finset.univ.erase x by
      ext w; simp [SimpleGraph.mem_neighborFinset, eq_comm]]
    simp
  simp only [lapMatrix, degMatrix, adjMatrix_top, Matrix.sub_apply, of_apply,
    Matrix.diagonal_apply]
  split_ifs with h
  · subst h; simp [hdeg, Nat.cast_sub this]
  · simp [h]
end MatrixTree
