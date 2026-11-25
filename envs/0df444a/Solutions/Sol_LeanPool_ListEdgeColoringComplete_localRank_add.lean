-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.localRank_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:08:16.457657+00:00
-- url     : https://prove2.me/submissions/6e7e447e-7dbc-421a-80f3-d9d47ac4cc74

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n u v w : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    localRank n u v + localRank n v u = targetDegree n u v := by
  unfold localRank IsLowEnd targetDegree diagIndex
  split_ifs <;> omega
end LeanPool.ListEdgeColoringComplete
