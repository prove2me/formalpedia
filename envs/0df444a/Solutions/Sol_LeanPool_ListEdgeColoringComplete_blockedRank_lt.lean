-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.blockedRank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:15:18.775896+00:00
-- url     : https://prove2.me/submissions/56736679-7a00-4c3c-874f-3449bfd4640d

module
public import Mathlib.Data.Fintype.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (n i : ℕ) (hn : 2 ≤ n) (hi : i < n) :
    blockedRank n i < n := by
  unfold blockedRank
  split <;> omega
end LeanPool.ListEdgeColoringComplete
