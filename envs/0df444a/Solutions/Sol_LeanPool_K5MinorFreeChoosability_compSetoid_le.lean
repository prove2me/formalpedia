-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.compSetoid_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:16.156288+00:00
-- url     : https://prove2.me/submissions/dcd57dcb-d95a-4280-a267-c17a7316b2ed

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
theorem _root_.solution (r : Setoid D) {σ α : Perm D} (hσ : ∀ z, r z (σ z))
    (hα : ∀ z, r z (α z)) {a b : D} (h : compSetoid σ α a b) : r a b := by
  change Relation.EqvGen _ a b at h
  induction h with
  | rel x y hxy =>
    rcases hxy with rfl | rfl
    · exact hσ x
    · exact hα x
  | refl x => exact r.refl x
  | symm x y _ ih => exact r.symm ih
  | trans x y z _ _ ih1 ih2 => exact r.trans ih1 ih2
end LeanPool.K5MinorFreeChoosability
