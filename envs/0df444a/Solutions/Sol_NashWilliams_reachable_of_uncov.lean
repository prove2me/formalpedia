-- Prove2me | solution 1 for NashWilliams.reachable_of_uncov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:52:03.680116+00:00
-- url     : https://prove2.me/submissions/f7010900-e064-4336-83c4-f53075b1a118

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Theorems.Thm_NashWilliams_total_update
public import Theorems.Thm_NashWilliams_Uncov_adj_iff

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable (G : SimpleGraph V) {k : ℕ}
variable {G}
namespace NashWilliams
theorem _root_.solution [Finite V] {F : Fin k → SimpleGraph V} (hF : Valid G F)
    (hmax : ∀ F' : Fin k → SimpleGraph V, Valid G F' → total F' ≤ total F) {u v : V}
    (huv : Uncov G F u v) (i : Fin k) :
    (F i).Reachable u v := by
  by_contra h
  have hval : Valid G (update F i (F i ⊔ edge u v)) := by
    refine hF.update i (sup_le (hF.1 i).1 ((edge_le_iff _).2 (Or.inr huv.1)))
      ((hF.1 i).2.sup_edge_of_not_reachable h) fun a b hab ↦ ?_
    rcases hab with hab | hab
    · exact Or.inl hab
    · right
      intro j
      apply huv.adj_iff
      rw [edge_adj] at hab
      rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
  have h1 := total_update F i (F i ⊔ edge u v)
  have h2 : (F i ⊔ edge u v).edgeSet.ncard = (F i).edgeSet.ncard + 1 := by
    rw [edgeSet_sup, edgeSet_edge_of_ne huv.1.ne,
      Set.ncard_union_eq
        (Set.disjoint_singleton_right.2 (show s(u, v) ∉ (F i).edgeSet from huv.2 i))
        (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton]
  have h3 := hmax _ hval
  omega
end NashWilliams
