-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.addPairSetoid_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:12.646421+00:00
-- url     : https://prove2.me/submissions/32cea785-9390-4c69-967b-71cfe62906d2

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
theorem _root_.solution (s : Setoid α) (x y : α) : addPairSetoid s x y x y :=
  Or.inr (Or.inl ⟨s.refl x, s.refl y⟩)
end LeanPool.K5MinorFreeChoosability
