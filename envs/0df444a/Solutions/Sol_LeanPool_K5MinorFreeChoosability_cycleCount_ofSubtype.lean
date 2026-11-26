-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.cycleCount_ofSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:25.837626+00:00
-- url     : https://prove2.me/submissions/a4c0334b-bcbf-4b61-b1e1-aa5526aa80e4

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_eq_restrict


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable (p : D → Prop) [DecidablePred p]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite D] (π : Perm (Subtype p)) :
    cycleCount (ofSubtype π) = cycleCount π + Nat.card {x // ¬ p x} := by
  refine numClasses_eq_restrict _ p _ (fun a b => ?_) (fun a b ha h => ?_)
  · change SameCycle π a b ↔ SameCycle (ofSubtype π) a b
    conv_lhs => rw [← subtypePerm_ofSubtype π]
    exact sameCycle_subtypePerm
  · exact h.eq_of_left (ofSubtype_apply_of_not_mem π ha)
end LeanPool.K5MinorFreeChoosability
