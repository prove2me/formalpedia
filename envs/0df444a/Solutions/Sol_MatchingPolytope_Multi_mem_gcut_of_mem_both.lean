-- Prove2me | solution 1 for MatchingPolytope.Multi.mem_gcut_of_mem_both
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:17.11744+00:00
-- url     : https://prove2.me/submissions/ce18dd3c-8bac-42ea-8df6-ada0bb524b99

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
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
theorem _root_.solution (hV : Valid ends W F) {S : Finset V} {e : E}
    (h1 : e ∈ shrinkF ends F S) (h2 : e ∈ shrinkF ends F (W \ S)) : e ∈ gcut ends F S := by
  obtain ⟨heF, u, hu, huS⟩ := mem_shrinkF.1 h1
  obtain ⟨-, u', hu', hu'S⟩ := mem_shrinkF.1 h2
  have : u' ∈ S := by
    by_contra h
    exact hu'S (Finset.mem_sdiff.2 ⟨hV.sub e heF u' hu', h⟩)
  simp only [gcut, Finset.mem_filter]
  exact ⟨heF, ⟨u', hu', this⟩, ⟨u, hu, huS⟩⟩
end MatchingPolytope.Multi
