-- Prove2me | solution 1 for MatchingPolytope.Multi.filter_collapse_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:09.332498+00:00
-- url     : https://prove2.me/submissions/c774a131-a184-4f9f-8c1c-c4767e4aa5e9

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution {R : Finset V} {r : V} (hr : r ∈ R) (hRW : R ⊆ W)
    (hRodd : Odd R.card) {T : Finset V} (hT : T ⊆ shrinkW W R r) (hTodd : Odd T.card) :
    Odd (W.filter fun u => collapse R r u ∈ T).card := by
  by_cases hrT : r ∈ T
  · have hU : W.filter (fun u => collapse R r u ∈ T) = R ∪ T.erase r := by
      ext u
      rw [Finset.mem_filter]
      simp only [Finset.mem_union, Finset.mem_erase, collapse]
      constructor
      · rintro ⟨-, h⟩
        split_ifs at h with hu
        · exact Or.inl hu
        · exact Or.inr ⟨fun h' => hu (h' ▸ hr), h⟩
      · rintro (hu | ⟨hur, hu⟩)
        · exact ⟨hRW hu, by simp [hu, hrT]⟩
        · have := hT hu
          simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff] at this
          rcases this with h | ⟨huW, huR⟩
          · exact absurd h hur
          · exact ⟨huW, by simp [huR, hu]⟩
    have hdisj : Disjoint R (T.erase r) := by
      rw [Finset.disjoint_left]
      intro u hu hu'
      rw [Finset.mem_erase] at hu'
      have := hT hu'.2
      simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff] at this
      rcases this with h | ⟨-, huR⟩
      · exact hu'.1 h
      · exact huR hu
    rw [hU, Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hrT]
    obtain ⟨k, hk⟩ := hTodd
    rw [hk]
    simpa using hRodd.add_even (even_two_mul k)
  · have hU : W.filter (fun u => collapse R r u ∈ T) = T := by
      ext u
      rw [Finset.mem_filter]
      simp only [collapse]
      constructor
      · rintro ⟨-, h⟩
        split_ifs at h with hu
        · exact absurd h hrT
        · exact h
      · intro hu
        have := hT hu
        simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff] at this
        rcases this with h | ⟨huW, huR⟩
        · exact absurd (h ▸ hu) hrT
        · exact ⟨huW, by simp [huR, hu]⟩
    rw [hU]; exact hTodd
end MatchingPolytope.Multi
