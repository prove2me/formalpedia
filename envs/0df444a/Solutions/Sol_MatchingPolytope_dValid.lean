-- Prove2me | solution 1 for MatchingPolytope.dValid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:31:37.173307+00:00
-- url     : https://prove2.me/submissions/c6f189a2-64fc-4b64-8b39-b6af046d5f56

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_valid_edgeSet


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [DecidableEq V]
namespace MatchingPolytope
theorem _root_.solution : Valid (dEnds G) univ univ := by
  refine ⟨fun _ _ _ _ => Finset.mem_univ _, fun e _ => ?_⟩
  rcases e with e | e | v
  · obtain ⟨a, b, hab, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    simp only [edgeEnds] at h
    simpa [dEnds, h] using hab
  · obtain ⟨a, b, hab, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    simp only [edgeEnds] at h
    simpa [dEnds, h] using hab
  · simp [dEnds]
end MatchingPolytope
