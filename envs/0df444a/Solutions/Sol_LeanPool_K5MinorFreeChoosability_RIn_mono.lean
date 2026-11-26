-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:53.064031+00:00
-- url     : https://prove2.me/submissions/cdc8caa9-70a4-4cf5-9e7c-0dc0da8a28ab

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
theorem _root_.solution (h : RIn G s a b) (hG : G ≤ G') (hs : s ⊆ t) : RIn G' t a b := by
  induction h with
  | refl => exact refl _
  | tail _ hbc ih => exact ih.tail (hG hbc.1) (hs hbc.2.1) (hs hbc.2.2)
end LeanPool.K5MinorFreeChoosability.RIn
