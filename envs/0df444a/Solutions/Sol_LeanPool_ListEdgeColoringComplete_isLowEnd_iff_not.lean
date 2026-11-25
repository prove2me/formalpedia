-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.isLowEnd_iff_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:14:54.078257+00:00
-- url     : https://prove2.me/submissions/2de44b23-4dcb-4e79-a22c-70fb6b5a6839

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
theorem _root_.solution (hv : v < n) (huv : u ≠ v) :
    IsLowEnd n u v ↔ ¬ IsLowEnd n v u := by
  unfold IsLowEnd diagIndex
  split_ifs <;> omega
end LeanPool.ListEdgeColoringComplete
