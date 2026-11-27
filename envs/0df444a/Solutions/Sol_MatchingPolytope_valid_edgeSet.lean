-- Prove2me | solution 1 for MatchingPolytope.valid_edgeSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:39.972284+00:00
-- url     : https://prove2.me/submissions/e808c321-5b58-43f5-a1df-50df6ad8331f

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
theorem _root_.solution : Valid (edgeEnds G) univ univ :=
  ⟨fun _ _ _ _ => Finset.mem_univ _, fun e _ => G.not_isDiag_of_mem_edgeSet e.2⟩
end MatchingPolytope
