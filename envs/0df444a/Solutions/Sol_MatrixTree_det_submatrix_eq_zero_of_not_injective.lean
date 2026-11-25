-- Prove2me | solution 1 for MatrixTree.det_submatrix_eq_zero_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:06:47.013437+00:00
-- url     : https://prove2.me/submissions/a2e747ee-706f-40a6-a87c-b245b52748dc

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution {R : Type*} [CommRing R] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) R) (p : Fin m → Fin k) (hp : ¬ Function.Injective p) :
    (A.submatrix id p).det = 0 := by
  simp only [Function.Injective, not_forall] at hp
  obtain ⟨i, j, hij, hne⟩ := hp
  exact det_zero_of_column_eq hne (fun l => by simp [hij])
end MatrixTree
