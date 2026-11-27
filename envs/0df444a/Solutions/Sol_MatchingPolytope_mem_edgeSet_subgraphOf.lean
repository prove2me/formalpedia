-- Prove2me | solution 1 for MatchingPolytope.mem_edgeSet_subgraphOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:20.040216+00:00
-- url     : https://prove2.me/submissions/f7fae071-3882-4787-abe5-02bccf7a4a3b

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Theorems.Thm_MatchingPolytope_Multi_exists_pair


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} (G : SimpleGraph V)
namespace MatchingPolytope
theorem _root_.solution {M : Finset G.edgeSet} {e : G.edgeSet} :
    (e : Sym2 V) ∈ (subgraphOf G M).edgeSet ↔ e ∈ M := by
  obtain ⟨a, b, hab⟩ := exists_pair (e : Sym2 V)
  rw [hab, SimpleGraph.Subgraph.mem_edgeSet]
  constructor
  · rintro ⟨e', he', h⟩
    have : e' = e := Subtype.ext (h.trans hab.symm)
    exact this ▸ he'
  · intro he
    exact ⟨e, he, hab⟩
end MatchingPolytope
