-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.numClasses_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:51.788822+00:00
-- url     : https://prove2.me/submissions/ddf09271-5897-4e37-8d43-a9d3e7c54762

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
theorem _root_.solution [Finite α] (s : Setoid α) : numClasses s ≤ Nat.card α :=
  Nat.card_le_card_of_surjective (Quotient.mk s) Quotient.mk_surjective
end LeanPool.K5MinorFreeChoosability
