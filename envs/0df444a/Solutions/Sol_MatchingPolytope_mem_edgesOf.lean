-- Prove2me | solution 1 for MatchingPolytope.mem_edgesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:42.304895+00:00
-- url     : https://prove2.me/submissions/a88dd45d-7a2a-4bf6-9132-d53de7599ba0

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution {M : G.Subgraph} {e : G.edgeSet} :
    e ∈ edgesOf G M ↔ (e : Sym2 V) ∈ M.edgeSet := by
  classical
  simp [edgesOf]
end MatchingPolytope
