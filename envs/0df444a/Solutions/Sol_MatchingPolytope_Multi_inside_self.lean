-- Prove2me | solution 1 for MatchingPolytope.Multi.inside_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:05.855975+00:00
-- url     : https://prove2.me/submissions/e0bda8d4-2bb6-4757-9f07-101f05fda8b4

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_mem_inside_of_pair
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_Multi_inside_subset

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) : inside ends D W = D := by
  ext e
  constructor
  · exact fun h => inside_subset D W h
  · intro he
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_inside_of_pair hab]
    exact ⟨he, ha, hb⟩
end MatchingPolytope.Multi
