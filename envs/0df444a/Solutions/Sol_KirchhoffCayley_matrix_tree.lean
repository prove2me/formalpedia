-- Prove2me | solution 1 for KirchhoffCayley.matrix_tree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:54:42.413949+00:00
-- url     : https://prove2.me/submissions/5f823bef-4356-4a6a-9d62-80cac075f3e3

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Definitions.Def_MatrixTree_Solution
public import Theorems.Thm_MatrixTree_matrix_tree


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open KirchhoffCayley
namespace KirchhoffCayley
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (Nat.card {H : SimpleGraph V // H ≤ G ∧ H.IsTree} : ℤ) =
      ((G.lapMatrix ℤ).submatrix (Subtype.val : {u // u ≠ v} → V) Subtype.val).det :=
  MatrixTree.matrix_tree G v
end KirchhoffCayley
