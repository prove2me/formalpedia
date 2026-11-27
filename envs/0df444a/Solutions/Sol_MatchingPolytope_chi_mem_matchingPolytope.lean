-- Prove2me | solution 1 for MatchingPolytope.chi_mem_matchingPolytope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:15.549886+00:00
-- url     : https://prove2.me/submissions/d681dd95-36a9-4498-b044-abcb553b4cfa

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_sum_chi_innerEdges
public import Theorems.Thm_MatchingPolytope_Multi_sum_chi_gcut
public import Theorems.Thm_MatchingPolytope_Multi_sum_degree
public import Theorems.Thm_MatchingPolytope_gcut_eq_cutEdges
public import Theorems.Thm_MatchingPolytope_valid_edgeSet


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution {M : Finset G.edgeSet}
    (hM : ∀ v, (gcut (edgeEnds G) M {v}).card ≤ 1) : chi M ∈ matchingPolytope G := by
  refine ⟨fun e => ?_, fun v => ?_, fun S hS => ?_⟩
  · unfold chi; split_ifs <;> norm_num
  · rw [← gcut_eq_cutEdges, sum_chi_gcut (Finset.subset_univ M)]
    exact_mod_cast hM v
  · rw [sum_chi_innerEdges]
    have h := sum_degree (β := ℕ) (valid_edgeSet G) (Finset.subset_univ M) S (fun _ => 1)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    have hle : ∑ v ∈ S, (gcut (edgeEnds G) M {v}).card ≤ ∑ v ∈ S, 1 :=
      Finset.sum_le_sum fun v _ => hM v
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hle
    obtain ⟨k, hk⟩ := hS
    have : 2 * (inside (edgeEnds G) M S).card ≤ 2 * k := by omega
    have h' : ((inside (edgeEnds G) M S).card : ℝ) ≤ k := by exact_mod_cast (by omega)
    rw [hk]
    push_cast
    linarith
end MatchingPolytope
