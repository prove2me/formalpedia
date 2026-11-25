-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.lowEnd_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:15:16.051127+00:00
-- url     : https://prove2.me/submissions/9a056c21-df2a-46b9-8bbf-1f4d2d3068f1

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
theorem _root_.solution (hu : u < n) (hv : v < n) : lowEnd n u v < n := by
  unfold lowEnd
  split_ifs <;> omega
end LeanPool.ListEdgeColoringComplete
