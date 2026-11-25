-- Prove2me | solution 1 for Menger.Aux.walk_in_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:10:17.436791+00:00
-- url     : https://prove2.me/submissions/7816501b-a459-4d95-a72a-9afc35d183e2

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
theorem _root_.solution {G : SimpleGraph V} (e : G.edgeSet) {z m : V} (hz : z ∈ (e : Sym2 V))
    (hm : m ∈ (e : Sym2 V)) : ∃ r : G.Walk z m, ∀ f ∈ r.edges, f = (e : Sym2 V) := by
  by_cases h : z = m
  · subst h
    exact ⟨.nil, by simp⟩
  · have he : (e : Sym2 V) = s(z, m) := (Sym2.mem_and_mem_iff h).1 ⟨hz, hm⟩
    have hadj : G.Adj z m := by rw [← G.mem_edgeSet, ← he]; exact e.2
    exact ⟨.cons hadj .nil, by simp [he]⟩
end Menger.Aux
