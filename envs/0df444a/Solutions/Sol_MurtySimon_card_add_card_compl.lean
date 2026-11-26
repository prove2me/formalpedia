-- Prove2me | solution 1 for MurtySimon.card_add_card_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:20:26.295881+00:00
-- url     : https://prove2.me/submissions/a7e7c406-7ac8-4fbb-82cb-7a019002e5ed

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_OnPath_ne


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset + #Gᶜ.edgeFinset = (Fintype.card V).choose 2 := by
  rw [← card_edgeFinset_top_eq_card_choose_two, ← card_union_of_disjoint]
  · congr 1
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_union, mem_edgeFinset, mem_edgeSet, compl_adj, top_adj]
      constructor
      · rintro (h | h)
        · exact h.ne
        · exact h.1
      · intro h
        by_cases hab : G.Adj a b
        · exact Or.inl hab
        · exact Or.inr ⟨h, hab⟩
  · rw [Finset.disjoint_left]
    intro e he he'
    rw [mem_edgeFinset] at he he'
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at he he'
      exact (compl_adj G a b).1 he' |>.2 he
end MurtySimon
