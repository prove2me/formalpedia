-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.connSet_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:35.668256+00:00
-- url     : https://prove2.me/submissions/b99472df-044c-43e1-bb5e-a38ff05d0cf9

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_refl
attribute [local refl] LeanPool.K5MinorFreeChoosability.RIn.refl

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (G : SimpleGraph W) (a : W) : ConnSet G {a} :=
  ⟨⟨a, rfl⟩, fun x hx y hy => by
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy; exact RIn.refl _⟩
end LeanPool.K5MinorFreeChoosability
