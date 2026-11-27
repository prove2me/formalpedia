-- Prove2me | solution 1 for MatchingPolytope.Multi.isPM_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:55.197495+00:00
-- url     : https://prove2.me/submissions/7e98f194-5cef-4395-8b59-e07f87ca70d2

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
public import Theorems.Thm_MatchingPolytope_Multi_gcut_union
public import Theorems.Thm_MatchingPolytope_Multi_gcut_subset
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton
public import Theorems.Thm_MatchingPolytope_Multi_mem_shrinkF
public import Theorems.Thm_MatchingPolytope_Multi_shrinkF_subset


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [DecidableEq V]
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq E] (hV : Valid ends W F) {S : Finset V} {M N : Finset E}
    (hM : M ⊆ shrinkF ends F S) (hN : N ⊆ shrinkF ends F (W \ S))
    (hcut : gcut ends M S = gcut ends N S)
    (hMdeg : ∀ v ∈ W, v ∉ S → (gcut ends M {v}).card = 1)
    (hNdeg : ∀ v ∈ W, v ∈ S → (gcut ends N {v}).card = 1) :
    IsPM ends W F (M ∪ N) := by
  have hMF : M ⊆ F := hM.trans (shrinkF_subset _)
  have hNF : N ⊆ F := hN.trans (shrinkF_subset _)
  refine ⟨Finset.union_subset hMF hNF, fun v hv => ?_⟩
  rw [gcut_union]
  by_cases hvS : v ∈ S
  · have : gcut ends M {v} ⊆ gcut ends N {v} := by
      intro e he
      rw [mem_gcut_singleton hV hMF] at he
      obtain ⟨heM, hve⟩ := he
      obtain ⟨-, u, hu, huS⟩ := mem_shrinkF.1 (hM heM)
      have : e ∈ gcut ends M S := by
        simp only [gcut, Finset.mem_filter]
        exact ⟨heM, ⟨v, hve, hvS⟩, ⟨u, hu, huS⟩⟩
      rw [hcut] at this
      rw [mem_gcut_singleton hV hNF]
      exact ⟨gcut_subset _ _ this, hve⟩
    rw [Finset.union_eq_right.2 this]
    exact hNdeg v hv hvS
  · have : gcut ends N {v} ⊆ gcut ends M {v} := by
      intro e he
      rw [mem_gcut_singleton hV hNF] at he
      obtain ⟨heN, hve⟩ := he
      obtain ⟨-, u, hu, huS⟩ := mem_shrinkF.1 (hN heN)
      have huS' : u ∈ S := by
        by_contra h
        exact huS (Finset.mem_sdiff.2 ⟨hV.sub e (hNF heN) u hu, h⟩)
      have : e ∈ gcut ends N S := by
        simp only [gcut, Finset.mem_filter]
        exact ⟨heN, ⟨u, hu, huS'⟩, ⟨v, hve, hvS⟩⟩
      rw [← hcut] at this
      rw [mem_gcut_singleton hV hMF]
      exact ⟨gcut_subset _ _ this, hve⟩
    rw [Finset.union_eq_left.2 this]
    exact hMdeg v hv hvS
end MatchingPolytope.Multi
