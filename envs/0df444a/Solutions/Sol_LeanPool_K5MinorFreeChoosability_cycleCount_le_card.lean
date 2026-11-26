-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.cycleCount_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:16:35.420729+00:00
-- url     : https://prove2.me/submissions/03e2eba8-62b4-44be-85e3-9ce70acefc53

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_le_card

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
omit [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite α] (π : Perm α) : cycleCount π ≤ Nat.card α :=
  numClasses_le_card _
end LeanPool.K5MinorFreeChoosability
