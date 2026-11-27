-- Prove2me | solution 1 for MatchingPolytope.Multi.mem_shrinkF_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:36.262669+00:00
-- url     : https://prove2.me/submissions/e4b294d7-6311-442e-80ae-ac5d410fbf6e

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_Multi_mem_shrinkF


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [DecidableEq V]
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {S : Finset V} {e : E} (he : e ∈ F) :
    e ∈ shrinkF ends F S ∨ e ∈ shrinkF ends F (W \ S) := by
  obtain ⟨a, b, -, ha, -, h⟩ := hV.pair he
  by_cases haS : a ∈ S
  · right; exact mem_shrinkF.2 ⟨he, a, by simp [h], fun h' => (Finset.mem_sdiff.1 h').2 haS⟩
  · left; exact mem_shrinkF.2 ⟨he, a, by simp [h], haS⟩
end MatchingPolytope.Multi
