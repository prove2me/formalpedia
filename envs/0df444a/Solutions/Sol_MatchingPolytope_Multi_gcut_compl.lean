-- Prove2me | solution 1 for MatchingPolytope.Multi.gcut_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:41.226869+00:00
-- url     : https://prove2.me/submissions/b5825b98-21c8-4811-9516-0488a361c13a

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_of_pair
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_Multi_gcut_subset

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq V] (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) (S : Finset V) :
    gcut ends D (W \ S) = gcut ends D S := by
  ext e
  constructor
  · intro h
    have he := gcut_subset D _ h
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_gcut_of_pair hab] at h ⊢
    simp only [Finset.mem_sdiff] at h
    tauto
  · intro h
    have he := gcut_subset D _ h
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_gcut_of_pair hab] at h ⊢
    simp only [Finset.mem_sdiff]
    tauto
end MatchingPolytope.Multi
