-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.compSetoid_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:23.767466+00:00
-- url     : https://prove2.me/submissions/d920bbdc-7c79-4cca-944c-10ce0c4924b3

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
theorem _root_.solution (σ α : Perm D) (z : D) : compSetoid σ α z (α z) :=
  Relation.EqvGen.rel _ _ (Or.inr rfl)
end LeanPool.K5MinorFreeChoosability
