-- Prove2me | solution 1 for MatchingPolytope.Multi.gcut_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:24:14.490399+00:00
-- url     : https://prove2.me/submissions/01a36294-8e62-4cb5-bb41-b74e5e7059bd

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
public import Theorems.Thm_MatchingPolytope_Multi_mem_shrinkF
public import Theorems.Thm_MatchingPolytope_Multi_shrinkF_subset
public import Theorems.Thm_MatchingPolytope_Multi_shrinkEnds_pair
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_Multi_gcut_subset
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_of_pair


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) (R : Finset V) (r : V)
    (T : Finset V) :
    gcut (shrinkEnds ends R r) (shrinkF ends D R) T =
      gcut ends D (W.filter fun u => collapse R r u ∈ T) := by
  ext e
  constructor
  · intro h
    have he := shrinkF_subset R (gcut_subset _ _ h)
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_gcut_of_pair (shrinkEnds_pair hab), mem_shrinkF] at h
    rw [mem_gcut_of_pair hab]
    simp only [Finset.mem_filter, ha, hb, true_and]
    exact ⟨he, h.2⟩
  · intro h
    have he := gcut_subset _ _ h
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_gcut_of_pair hab] at h
    simp only [Finset.mem_filter, ha, hb, true_and] at h
    rw [mem_gcut_of_pair (shrinkEnds_pair hab), mem_shrinkF]
    refine ⟨⟨he, ?_⟩, h.2⟩
    rw [hab]
    by_contra hcon
    simp only [Sym2.mem_iff, exists_eq_or_imp, exists_eq_left, not_or, not_not] at hcon
    simp only [collapse, hcon.1, hcon.2, ↓reduceIte] at h
    tauto
end MatchingPolytope.Multi
