-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.compSetoid_of_sameCycle_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:16:17.74887+00:00
-- url     : https://prove2.me/submissions/0da7f935-a3b8-4a93-87d2-61ac486c9891

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_left
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_step


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {σ α : Perm D} {a b : D} (h : SameCycle σ a b) :
    compSetoid σ α a b :=
  sameCycle_of_step _ (compSetoid_left σ α) h
end LeanPool.K5MinorFreeChoosability
