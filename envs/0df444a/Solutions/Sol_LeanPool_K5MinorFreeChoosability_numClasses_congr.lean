-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.numClasses_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:46.979768+00:00
-- url     : https://prove2.me/submissions/07cc72f7-ca30-4591-abfe-f87ebf5e1ef7

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
theorem _root_.solution {s t : Setoid α} (h : ∀ a b, s a b ↔ t a b) :
    numClasses s = numClasses t := by
  have : s = t := Setoid.ext h
  subst this; rfl
end LeanPool.K5MinorFreeChoosability
