-- Prove2me | solution 2 for Menger.Aux.lower_from_lineGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:51:38.085275+00:00
-- url     : https://prove2.me/submissions/c5e36f76-955a-4d3b-8725-76109a8348bb

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Theorems.Thm_Menger_Aux_walk_in_edge

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution {G : SimpleGraph V} :
    ∀ {e f : G.edgeSet} (q : G.lineGraph.Walk e f) {z z' : V}, z ∈ (e : Sym2 V) →
      z' ∈ (f : Sym2 V) → ∃ r : G.Walk z z', ∀ g ∈ r.edges, ∃ e'' ∈ q.support, g = (e'' : Sym2 V)
  | _, _, .nil, _, _, hz, hz' => by
    obtain ⟨r, hr⟩ := walk_in_edge _ hz hz'
    exact ⟨r, fun g hg => ⟨_, Walk.start_mem_support _, hr g hg⟩⟩
  | e, _, .cons h q, _, _, hz, hz' => by
    obtain ⟨-, m, hm1, hm2⟩ := lineGraph_adj_iff_exists.1 h
    obtain ⟨r1, hr1⟩ := walk_in_edge e hz hm1
    obtain ⟨r2, hr2⟩ := solution q hm2 hz'
    refine ⟨r1.append r2, fun g hg => ?_⟩
    rw [Walk.edges_append, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ⟨e, by simp, hr1 g hg⟩
    · obtain ⟨e'', he'', rfl⟩ := hr2 g hg
      exact ⟨e'', by simp [he''], rfl⟩
end Menger.Aux
