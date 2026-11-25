-- Prove2me | solution 1 for NashWilliams.card_image_le_ncard_crossing_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:51:21.185987+00:00
-- url     : https://prove2.me/submissions/1d85aca4-2f8d-4951-a2a1-f0d84c6ceb75

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Theorems.Thm_NashWilliams_reachable_map_of_adj

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
namespace NashWilliams
theorem _root_.solution [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    (hT : T.Connected) (f : V → V) :
    #(univ.image f) ≤ (T.edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet).ncard + 1 := by
  set W := ↥(univ.image f)
  let g : V → W := fun a ↦ ⟨f a, mem_image_of_mem _ (mem_univ a)⟩
  let Q : SimpleGraph W := SimpleGraph.fromRel fun p q ↦ ∃ a b, T.Adj a b ∧ g a = p ∧ g b = q
  have hg : ∀ p : W, ∃ a, g a = p := by
    rintro ⟨p, hp⟩
    obtain ⟨a, -, rfl⟩ := mem_image.1 hp
    exact ⟨a, rfl⟩
  have hQ : Q.Connected := by
    have : Nonempty V := hT.nonempty
    have : Nonempty W := ⟨g (Classical.arbitrary V)⟩
    refine Connected.mk fun p q ↦ ?_
    obtain ⟨a, rfl⟩ := hg p
    obtain ⟨b, rfl⟩ := hg q
    refine reachable_map_of_adj g (fun x y hxy ↦ ?_) (hT.preconnected a b)
    by_cases hxy' : g x = g y
    · rw [hxy']
    · exact Adj.reachable ((fromRel_adj _ _ _).2 ⟨hxy', Or.inl ⟨x, y, hxy, rfl, rfl⟩⟩)
  have h1 := hQ.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
  have h2 : Q.edgeSet ⊆ Sym2.map g '' (T.edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet) := by
    intro e he
    induction e using Sym2.ind with
    | _ p q =>
      have he' : Q.Adj p q := he
      obtain ⟨hpq, h | h⟩ := (fromRel_adj _ _ _).1 he'
      · obtain ⟨a, b, hab, rfl, rfl⟩ := h
        refine ⟨s(a, b), ⟨hab, ?_⟩, rfl⟩
        exact fun h' ↦ hpq (Subtype.ext h')
      · obtain ⟨a, b, hab, rfl, rfl⟩ := h
        refine ⟨s(a, b), ⟨hab, ?_⟩, Sym2.eq_swap⟩
        exact fun h' ↦ hpq (Subtype.ext h'.symm)
  have h3 := (Set.ncard_le_ncard h2 (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))
  omega
end NashWilliams
