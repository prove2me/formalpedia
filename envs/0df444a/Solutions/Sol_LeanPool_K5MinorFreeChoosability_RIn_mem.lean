-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:31.582439+00:00
-- url     : https://prove2.me/submissions/7be79dd7-59c0-4aac-a225-30db444f8024

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_refl
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_tail
attribute [local refl] LeanPool.K5MinorFreeChoosability.RIn.refl

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}
namespace LeanPool.K5MinorFreeChoosability.RIn
theorem _root_.solution (h : RIn G s a b) (ha : a ∈ s) : b ∈ s := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.2
end LeanPool.K5MinorFreeChoosability.RIn
