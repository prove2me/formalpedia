-- Prove2me | solution 1 for MatchingPolytope.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:46.444501+00:00
-- url     : https://prove2.me/submissions/15d7fe3d-086e-425d-af1a-307007ee1051

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_inside_eq_innerEdges
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_of_pair
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
theorem _root_.solution {x : G.edgeSet → ℝ} (hx : x ∈ matchingPolytope G) (A B : Finset V)
    (hodd : Odd (A \ B).card) :
    1 ≤ ∑ e ∈ cutEdges G A, x e + ∑ e ∈ cutEdges G B, x e +
      ∑ v ∈ univ.filter (fun v => ¬ (v ∈ A ↔ v ∈ B)), (1 - ∑ e ∈ cutEdges G {v}, x e) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  set S := A \ B with hS
  -- posimodularity of the cut function
  have hsub : cutEdges G S ⊆ cutEdges G A ∪ cutEdges G B := by
    intro e he
    rw [← gcut_eq_cutEdges] at he
    rw [Finset.mem_union, ← gcut_eq_cutEdges, ← gcut_eq_cutEdges]
    obtain ⟨a, b, -, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    rw [mem_gcut_of_pair h] at he
    rw [mem_gcut_of_pair h, mem_gcut_of_pair h]
    simp only [hS, Finset.mem_sdiff, Finset.mem_univ, true_and] at he ⊢
    tauto
  have h1 : ∑ e ∈ cutEdges G S, x e ≤ ∑ e ∈ cutEdges G A, x e + ∑ e ∈ cutEdges G B, x e := by
    calc ∑ e ∈ cutEdges G S, x e ≤ ∑ e ∈ cutEdges G A ∪ cutEdges G B, x e :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hx1 e)
      _ ≤ ∑ e ∈ cutEdges G A ∪ cutEdges G B, x e + ∑ e ∈ cutEdges G A ∩ cutEdges G B, x e :=
          le_add_of_nonneg_right (Finset.sum_nonneg fun e _ => hx1 e)
      _ = _ := Finset.sum_union_inter
  have h2 : ∑ v ∈ S, (1 - ∑ e ∈ cutEdges G {v}, x e) ≤
      ∑ v ∈ univ.filter (fun v => ¬ (v ∈ A ↔ v ∈ B)), (1 - ∑ e ∈ cutEdges G {v}, x e) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      simp only [hS, Finset.mem_sdiff] at hv
      simp [hv.1, hv.2]
    · intro v _ _
      linarith [hx2 v]
  have h3 := sum_degree (valid_edgeSet G) (D := univ) subset_rfl S x
  simp only [gcut_eq_cutEdges, inside_eq_innerEdges, nsmul_eq_mul] at h3
  have h4 := hx3 S hodd
  have h5 : ∑ v ∈ S, (1 - ∑ e ∈ cutEdges G {v}, x e) =
      (S.card : ℝ) - ∑ v ∈ S, ∑ e ∈ cutEdges G {v}, x e := by
    rw [Finset.sum_sub_distrib]; simp
  rw [h5, h3] at h2
  push_cast at h2
  linarith
end MatchingPolytope
