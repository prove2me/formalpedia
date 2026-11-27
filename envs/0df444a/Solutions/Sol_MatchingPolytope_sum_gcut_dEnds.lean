-- Prove2me | solution 1 for MatchingPolytope.sum_gcut_dEnds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:30.20097+00:00
-- url     : https://prove2.me/submissions/8eaaced8-5191-4c92-843d-0fac07c868ce

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_of_pair
public import Theorems.Thm_MatchingPolytope_gcut_eq_cutEdges
public import Theorems.Thm_MatchingPolytope_valid_edgeSet


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution (z : DEdge G → ℝ) (T : Finset (V ⊕ V)) :
    ∑ e ∈ gcut (dEnds G) univ T, z e =
      ∑ e ∈ cutEdges G (univ.filter fun v => Sum.inl v ∈ T), z (Sum.inl e) +
      ∑ e ∈ cutEdges G (univ.filter fun v => Sum.inr v ∈ T), z (Sum.inr (Sum.inl e)) +
      ∑ v ∈ univ.filter (fun v => ¬ (Sum.inl v ∈ T ↔ Sum.inr v ∈ T)),
        z (Sum.inr (Sum.inr v)) := by
  classical
  have hfil : ∀ {α : Type _} [Fintype α] (s : Finset α) (f : α → ℝ),
      ∑ a ∈ s, f a = ∑ a, if a ∈ s then f a else 0 := by
    intro α _ s f
    rw [← Finset.sum_filter]
    congr 1
    ext a; simp
  rw [hfil, Fintype.sum_sum_type, Fintype.sum_sum_type, hfil (cutEdges G _),
    hfil (cutEdges G _), hfil (univ.filter _), add_assoc]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    obtain ⟨a, b, -, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    simp only [edgeEnds] at h
    have h' : dEnds G (Sum.inl e) = s(Sum.inl a, Sum.inl b) := by simp [dEnds, h]
    rw [← gcut_eq_cutEdges]
    congr 1
    rw [mem_gcut_of_pair h', mem_gcut_of_pair (ends := edgeEnds G) h]
    simp
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    obtain ⟨a, b, -, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    simp only [edgeEnds] at h
    have h' : dEnds G (Sum.inr (Sum.inl e)) = s(Sum.inr a, Sum.inr b) := by simp [dEnds, h]
    rw [← gcut_eq_cutEdges]
    congr 1
    rw [mem_gcut_of_pair h', mem_gcut_of_pair (ends := edgeEnds G) h]
    simp
  · apply Finset.sum_congr rfl
    intro v _
    have h' : dEnds G (Sum.inr (Sum.inr v)) = s(Sum.inl v, Sum.inr v) := rfl
    congr 1
    rw [mem_gcut_of_pair h']
    simp only [Finset.mem_univ, true_and, Finset.mem_filter]
    exact propext (by tauto)
end MatchingPolytope
