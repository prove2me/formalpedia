-- Prove2me | solution 1 for MatchingPolytope.edmonds_matching_polytope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:37:52.171061+00:00
-- url     : https://prove2.me/submissions/2771e732-3ebc-44da-afac-d9a2cf5bd8de

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_chi_mem_matchingVectors
public import Theorems.Thm_MatchingPolytope_card_gcut_edgesOf_le
public import Theorems.Thm_MatchingPolytope_chi_mem_matchingPolytope
public import Theorems.Thm_MatchingPolytope_convex_matchingPolytope
public import Theorems.Thm_MatchingPolytope_dValid
public import Theorems.Thm_MatchingPolytope_dvec_mem_poly
public import Theorems.Thm_MatchingPolytope_chi_proj
public import Theorems.Thm_MatchingPolytope_card_gcut_proj_le
public import Theorems.Thm_MatchingPolytope_Multi_inHull_of_mem_poly
public import Theorems.Thm_MatchingPolytope_incidence_eq_chi


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution :
    convexHull ℝ (matchingVectors G) = matchingPolytope G := by
  apply le_antisymm
  · refine convexHull_min ?_ (convex_matchingPolytope G)
    rintro x ⟨M, hM, rfl⟩
    rw [incidence_eq_chi]
    exact chi_mem_matchingPolytope G (card_gcut_edgesOf_le G hM)
  · intro x hx
    obtain ⟨w, hw0, hw1, hw2, hw3⟩ := inHull_of_mem_poly _ _ _ (dValid G) (dvec_mem_poly G hx)
    have hxeq : x = ∑ N, w N • chi (proj G N) := by
      funext e
      have := congrFun hw3 (Sum.inl e)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dvec] at this
      rw [← this, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro N _
      simp only [Pi.smul_apply, smul_eq_mul, chi_proj]
    classical
    rw [hxeq, ← Finset.sum_filter_of_ne (p := fun N => w N ≠ 0)
      (fun N _ h h0 => h (by simp [h0]))]
    refine (convex_convexHull ℝ _).sum_mem (fun N _ => hw0 N) ?_ fun N hN => ?_
    · rw [Finset.sum_filter_ne_zero, hw2]
    · exact subset_convexHull ℝ _ (chi_mem_matchingVectors G
        (card_gcut_proj_le G (hw1 N (Finset.mem_filter.1 hN).2)))
end MatchingPolytope
