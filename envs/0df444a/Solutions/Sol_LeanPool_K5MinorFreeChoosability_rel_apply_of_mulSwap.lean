-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.rel_apply_of_mulSwap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:16:40.336954+00:00
-- url     : https://prove2.me/submissions/6ca046f7-22f5-4be2-a8f9-8cdaaa327498

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_addPair_apply_of_mulSwap

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable [DecidableEq D]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (s : Setoid D) (π : Perm D) (x y : D)
    (h : ∀ z, s z ((π * swap x y) z)) (hxy : s x y) (z : D) : s z (π z) := by
  rcases addPair_apply_of_mulSwap s π x y h z with k | ⟨k1, k2⟩ | ⟨k1, k2⟩
  · exact k
  · exact s.trans (s.trans k1 hxy) k2
  · exact s.trans (s.trans k1 (s.symm hxy)) k2
end LeanPool.K5MinorFreeChoosability
