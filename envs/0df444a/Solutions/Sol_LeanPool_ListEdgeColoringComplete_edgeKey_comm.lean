-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.edgeKey_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:21:41.295451+00:00
-- url     : https://prove2.me/submissions/2d4ac710-26b3-4dc3-a38b-2cb9c7d1e6ac

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_diagIndex_comm
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_lowEnd_comm

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n u v w : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (n u v : ℕ) :
    edgeKey n u v = edgeKey n v u := by
  unfold edgeKey
  rw [diagIndex_comm n u v, lowEnd_comm n u v]
end LeanPool.ListEdgeColoringComplete
