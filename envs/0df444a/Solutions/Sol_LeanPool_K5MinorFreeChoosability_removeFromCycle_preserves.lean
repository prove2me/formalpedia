-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.removeFromCycle_preserves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:06.589487+00:00
-- url     : https://prove2.me/submissions/a7a4df66-ec8b-4b11-84d6-04050d3e8ca9

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_apply
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_apply_self


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable (M : MinorModel G H) (inK : G.Dart → Prop)
variable {M inK}
variable [DecidableEq V]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {D β : Type*} [DecidableEq D] (f : D → β) {π : Perm D}
    (hf : ∀ u, f (π u) = f u) (z : D) (u : D) : f (removeFromCycle π z u) = f u := by
  by_cases huz : u = z
  · rw [huz, removeFromCycle_apply_self]
  · rw [removeFromCycle_apply π huz]
    split_ifs with h
    · rw [hf z, ← h, hf u]
    · exact hf u
end LeanPool.K5MinorFreeChoosability
