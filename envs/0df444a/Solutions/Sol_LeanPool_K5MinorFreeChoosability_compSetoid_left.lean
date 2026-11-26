-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.compSetoid_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:08.064842+00:00
-- url     : https://prove2.me/submissions/08b90a96-4afa-4524-91f1-8ac6bbf41fcb

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (σ α : Perm D) (z : D) : compSetoid σ α z (σ z) :=
  Relation.EqvGen.rel _ _ (Or.inl rfl)
end LeanPool.K5MinorFreeChoosability
