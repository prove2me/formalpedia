-- Prove2me | solution 1 for MatchingPolytope.Multi.gcut_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:05.263803+00:00
-- url     : https://prove2.me/submissions/4606ae7f-486b-41aa-9455-8b0e06096f64

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
theorem _root_.solution (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) : gcut ends D W = ∅ := by
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro h
  have he := gcut_subset D _ h
  obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
  rw [mem_gcut_of_pair hab] at h
  tauto
end MatchingPolytope.Multi
