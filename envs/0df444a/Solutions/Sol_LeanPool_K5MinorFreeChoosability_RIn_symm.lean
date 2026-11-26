-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:50.344521+00:00
-- url     : https://prove2.me/submissions/0941e59b-5599-44cf-aadd-fab6d62f8fbe

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_refl
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_tail
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_head
attribute [local refl] LeanPool.K5MinorFreeChoosability.RIn.refl

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}
namespace LeanPool.K5MinorFreeChoosability.RIn
theorem _root_.solution (h : RIn G s a b) : RIn G s b a := by
  induction h with
  | refl => exact refl _
  | tail _ hbc ih => exact head hbc.1.symm hbc.2.2 hbc.2.1 ih
end LeanPool.K5MinorFreeChoosability.RIn
