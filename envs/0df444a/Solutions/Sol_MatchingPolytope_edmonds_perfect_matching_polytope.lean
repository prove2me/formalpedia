-- Prove2me | solution 1 for MatchingPolytope.edmonds_perfect_matching_polytope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:37:35.034349+00:00
-- url     : https://prove2.me/submissions/33d55810-de08-42f9-a9ff-08b3acc613af

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Theorems.Thm_MatchingPolytope_convex_poly
public import Theorems.Thm_MatchingPolytope_valid_edgeSet
public import Theorems.Thm_MatchingPolytope_edmondsPolytope_eq
public import Theorems.Thm_MatchingPolytope_incidence_eq_chi
public import Theorems.Thm_MatchingPolytope_isPM_edgesOf
public import Theorems.Thm_MatchingPolytope_chi_mem_perfectMatchingVectors
public import Theorems.Thm_MatchingPolytope_Multi_chi_mem_poly
public import Theorems.Thm_MatchingPolytope_Multi_inHull_of_mem_poly


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
namespace MatchingPolytope
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    convexHull ℝ (perfectMatchingVectors G) = edmondsPolytope G := by
  apply le_antisymm
  · rw [edmondsPolytope_eq]
    refine convexHull_min ?_ (convex_poly _ _ _)
    rintro x ⟨M, hM, rfl⟩
    rw [incidence_eq_chi]
    exact chi_mem_poly (valid_edgeSet G) (isPM_edgesOf G hM)
  · intro x hx
    rw [edmondsPolytope_eq] at hx
    obtain ⟨w, hw0, hw1, hw2, hw3⟩ := inHull_of_mem_poly _ _ _ (valid_edgeSet G) hx
    classical
    rw [← hw3, ← Finset.sum_filter_of_ne (p := fun M => w M ≠ 0)
      (fun M _ h h0 => h (by simp [h0]))]
    refine (convex_convexHull ℝ _).sum_mem (fun M _ => hw0 M) ?_ fun M hM => ?_
    · rw [Finset.sum_filter_ne_zero, hw2]
    · exact subset_convexHull ℝ _
        (chi_mem_perfectMatchingVectors G (hw1 M (Finset.mem_filter.1 hM).2))
end MatchingPolytope
