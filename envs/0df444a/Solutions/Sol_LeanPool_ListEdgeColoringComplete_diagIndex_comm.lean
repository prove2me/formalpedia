-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.diagIndex_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:08:42.333163+00:00
-- url     : https://prove2.me/submissions/074a4b84-5872-423b-b256-cd017fedfbbe

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
theorem _root_.solution (n u v : ℕ) : diagIndex n u v = diagIndex n v u := by
  unfold diagIndex
  rw [Nat.add_comm]
end LeanPool.ListEdgeColoringComplete
