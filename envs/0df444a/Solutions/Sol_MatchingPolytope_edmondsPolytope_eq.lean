-- Prove2me | solution 1 for MatchingPolytope.edmondsPolytope_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:20.452463+00:00
-- url     : https://prove2.me/submissions/3e9eb903-e41b-48c1-8e82-b59bc45cd3a5

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Theorems.Thm_MatchingPolytope_gcut_eq_cutEdges

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution [DecidableEq V] :
    edmondsPolytope G = Multi.Poly (edgeEnds G) univ univ := by
  ext x
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun e he => absurd (Finset.mem_univ e) he, h1, fun v _ => ?_, fun S _ hS => ?_⟩
    · rw [gcut_eq_cutEdges]; exact h2 v
    · rw [gcut_eq_cutEdges]; exact h3 S hS
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨h1, fun v => ?_, fun S hS => ?_⟩
    · rw [← gcut_eq_cutEdges]; exact h2 v (Finset.mem_univ v)
    · rw [← gcut_eq_cutEdges]; exact h3 S (Finset.subset_univ S) hS
end MatchingPolytope
