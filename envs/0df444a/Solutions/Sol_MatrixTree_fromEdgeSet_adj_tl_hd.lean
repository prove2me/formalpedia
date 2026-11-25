-- Prove2me | solution 1 for MatrixTree.fromEdgeSet_adj_tl_hd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:12:27.832094+00:00
-- url     : https://prove2.me/submissions/7bcb6b1d-63c9-4f9d-a7cf-8753268b6e0a

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_mk_tl_hd
public import Theorems.Thm_MatrixTree_tl_ne_hd

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace MatrixTree
theorem _root_.solution (v : V) (g : {u // u ≠ v} → Sym2 V) (hg : ∀ w, ¬ (g w).IsDiag)
    (w : {u // u ≠ v}) : (fromEdgeSet (Set.range g)).Adj (tl (g w)) (hd (g w)) := by
  rw [fromEdgeSet_adj, mk_tl_hd]
  exact ⟨⟨w, rfl⟩, tl_ne_hd (hg w)⟩
end MatrixTree
