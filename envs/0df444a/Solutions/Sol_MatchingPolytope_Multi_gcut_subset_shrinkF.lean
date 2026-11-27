-- Prove2me | solution 1 for MatchingPolytope.Multi.gcut_subset_shrinkF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:10.511678+00:00
-- url     : https://prove2.me/submissions/8b77c818-b03b-473b-8bbd-e33e4bafe01a

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
namespace MatchingPolytope.Multi
theorem _root_.solution {S R : Finset V} (h : ∀ u, u ∉ S → u ∉ R) :
    gcut ends F S ⊆ shrinkF ends F R := by
  intro e he
  simp only [gcut, Finset.mem_filter] at he
  obtain ⟨heF, -, u, hu, huS⟩ := he
  exact mem_shrinkF.2 ⟨heF, u, hu, h u huS⟩
end MatchingPolytope.Multi
