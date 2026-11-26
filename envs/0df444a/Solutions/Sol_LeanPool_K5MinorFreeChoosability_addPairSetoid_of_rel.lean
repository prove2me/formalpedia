-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.addPairSetoid_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:31.087226+00:00
-- url     : https://prove2.me/submissions/014bda91-9b19-4541-b743-3a4c436de03f

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {s : Setoid α} {x y a b : α} (h : s a b) :
    addPairSetoid s x y a b := Or.inl h
end LeanPool.K5MinorFreeChoosability
