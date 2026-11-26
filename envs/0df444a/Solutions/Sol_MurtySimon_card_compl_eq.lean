-- Prove2me | solution 1 for MurtySimon.card_compl_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:20:42.357003+00:00
-- url     : https://prove2.me/submissions/2b65f8e4-2979-4e91-901f-0cca16f0b45d

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_mem_Rt


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] :
    #Gᶜ.edgeFinset = #(Rt G) + #(Nc G) := by
  classical
  have hdisj : Disjoint (Rt G) (Nc G) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Nc, mem_filter] at hf'
    exact hf'.2.2 (mem_Rt.1 hf)
  rw [← card_union_of_disjoint hdisj]
  congr 1
  ext f
  simp only [mem_edgeFinset, mem_union, mem_Rt, Nc, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    by_cases hc : IsCrit G f
    · exact Or.inl hc
    · exact Or.inr ⟨h, hc⟩
  · rintro (h | h)
    · obtain ⟨x, y, u, rfl, hm⟩ := h
      rw [mem_edgeSet, compl_adj]; exact ⟨hm.1, hm.2.1⟩
    · exact h.1
end MurtySimon
