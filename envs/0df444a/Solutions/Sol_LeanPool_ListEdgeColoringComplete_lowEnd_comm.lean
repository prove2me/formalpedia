-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.lowEnd_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:15:09.914795+00:00
-- url     : https://prove2.me/submissions/57ff4b02-6e64-4860-962f-5a56f91bfc9d

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
theorem _root_.solution (n u v : ℕ) :
    lowEnd n u v = lowEnd n v u := by
  unfold lowEnd IsLowEnd diagIndex
  split_ifs <;> omega
end LeanPool.ListEdgeColoringComplete
