-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.targetDegree_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:15:26.189262+00:00
-- url     : https://prove2.me/submissions/af972a6b-0103-47ae-bc02-a75dc8ec223a

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
theorem _root_.solution (n u v : ℕ) : targetDegree n u v = targetDegree n v u := by
  unfold targetDegree
  rw [Nat.add_comm]
end LeanPool.ListEdgeColoringComplete
