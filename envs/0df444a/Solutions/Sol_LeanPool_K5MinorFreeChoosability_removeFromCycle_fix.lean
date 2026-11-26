-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.removeFromCycle_fix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:07.57281+00:00
-- url     : https://prove2.me/submissions/b01a2c86-de8a-486c-93e6-be411869e2cd

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_dartSymm_apply
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_apply
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
attribute [local simp] LeanPool.K5MinorFreeChoosability.dartSymm_apply
attribute [local simp] LeanPool.K5MinorFreeChoosability.restrict_adj



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
theorem _root_.solution {D : Type*} [DecidableEq D] {π : Perm D} {z u : D} (hu : π u = u)
    (huz : u ≠ z) : removeFromCycle π z u = u := by
  rw [removeFromCycle_apply π huz]
  simp [hu, huz]
end LeanPool.K5MinorFreeChoosability
