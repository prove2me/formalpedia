-- Prove2me | solution 2 for Menger.Aux.lift_to_lineGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:48:57.259889+00:00
-- url     : https://prove2.me/submissions/280b0b67-191c-48d4-8c9e-f6557a9d1b8f

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution {G : SimpleGraph V} :
    ∀ {w z : V} (p : G.Walk w z) (e : G.edgeSet), w ∈ (e : Sym2 V) →
      ∃ e' : G.edgeSet, z ∈ (e' : Sym2 V) ∧ ∃ q : G.lineGraph.Walk e e',
        ∀ f ∈ q.support, f = e ∨ (f : Sym2 V) ∈ p.edges
  | _, _, .nil, e, he => ⟨e, he, .nil, by simp⟩
  | _, _, .cons (v := w') h p, e, he => by
    obtain ⟨e', he', q, hq⟩ := solution p ⟨s(_, w'), h⟩ (Sym2.mem_mk_right _ _)
    by_cases heq : e = ⟨s(_, w'), h⟩
    · subst heq
      refine ⟨e', he', q, fun f hf => ?_⟩
      rcases hq f hf with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by simp [h1])
    · have hadj : G.lineGraph.Adj e ⟨s(_, w'), h⟩ :=
        lineGraph_adj_iff_exists.2 ⟨heq, _, he, Sym2.mem_mk_left _ _⟩
      refine ⟨e', he', .cons hadj q, fun f hf => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact Or.inl rfl
      rcases hq f hf with h1 | h1
      · exact Or.inr (by simp [h1])
      · exact Or.inr (by simp [h1])
end Menger.Aux
