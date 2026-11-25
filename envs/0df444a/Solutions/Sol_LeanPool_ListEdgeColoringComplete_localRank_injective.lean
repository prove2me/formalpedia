-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.localRank_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:08:17.314574+00:00
-- url     : https://prove2.me/submissions/d9ddd361-cb67-43ff-9805-00269f1c0066

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
theorem _root_.solution (hu : u < n) (hv : v < n) (hw : w < n) (huv : u ≠ v)
    (huw : u ≠ w) (h : localRank n u v = localRank n u w) : v = w := by
  revert h
  unfold localRank IsLowEnd targetDegree diagIndex
  split_ifs <;> omega
end LeanPool.ListEdgeColoringComplete
