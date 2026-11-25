-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.targetDegree_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:08:31.339354+00:00
-- url     : https://prove2.me/submissions/09e064e8-f8da-4df7-b2f2-2d2845c63ae4

module
public import Mathlib.Data.Fintype.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (n i j : ℕ) (hn : 2 ≤ n) :
    targetDegree n i j < n := by
  unfold targetDegree
  split <;> omega
end LeanPool.ListEdgeColoringComplete
