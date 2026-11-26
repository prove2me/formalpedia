-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.compSetoid_of_sameCycle_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:21.666746+00:00
-- url     : https://prove2.me/submissions/a1926502-b87a-4273-a9d2-3ebdcd80827c

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_left
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_right
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_step


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {σ α : Perm D} {a b : D} (h : SameCycle (σ * α) a b) :
    compSetoid σ α a b :=
  sameCycle_of_step _ (fun z => (compSetoid σ α).trans (compSetoid_right σ α z)
    (compSetoid_left σ α (α z))) h
end LeanPool.K5MinorFreeChoosability
