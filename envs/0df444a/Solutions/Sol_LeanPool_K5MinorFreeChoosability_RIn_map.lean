-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:24:13.117948+00:00
-- url     : https://prove2.me/submissions/11c92807-9b2d-4ac0-bddc-63723bf06021

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_refl
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_trans
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
theorem _root_.solution {W' : Type*} {G' : SimpleGraph W'} {t : Set W'} (f : W → W')
    (hf : ∀ x y, G.Adj x y → x ∈ s → y ∈ s → RIn G' t (f x) (f y))
    (h : RIn G s a b) : RIn G' t (f a) (f b) := by
  induction h with
  | refl => exact refl _
  | tail _ hbc ih => exact ih.trans (hf _ _ hbc.1 hbc.2.1 hbc.2.2)
end LeanPool.K5MinorFreeChoosability.RIn
