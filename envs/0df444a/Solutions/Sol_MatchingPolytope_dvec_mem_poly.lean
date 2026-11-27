-- Prove2me | solution 1 for MatchingPolytope.dvec_mem_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:35:39.85627+00:00
-- url     : https://prove2.me/submissions/e066e50e-3f0d-4b5e-8047-397681d576a4

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_sum_gcut_dEnds
public import Theorems.Thm_MatchingPolytope_cutEdges_empty
public import Theorems.Thm_MatchingPolytope_lower_bound

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution {x : G.edgeSet → ℝ} (hx : x ∈ matchingPolytope G) :
    dvec G x ∈ Multi.Poly (dEnds G) univ univ := by
  refine ⟨fun e he => absurd (Finset.mem_univ e) he, fun e => ?_, fun t _ => ?_,
    fun T _ hT => ?_⟩
  · rcases e with e | e | v
    · exact hx.1 e
    · exact hx.1 e
    · simp only [dvec]; linarith [hx.2.1 v]
  · rw [sum_gcut_dEnds]
    rcases t with v | v
    · have hA : (univ.filter fun u => (Sum.inl u : V ⊕ V) ∈ ({Sum.inl v} : Finset (V ⊕ V))) =
          {v} := by ext u; simp
      have hB : (univ.filter fun u => (Sum.inr u : V ⊕ V) ∈ ({Sum.inl v} : Finset (V ⊕ V))) =
          ∅ := by ext u; simp
      have hC : (univ.filter fun u => ¬ ((Sum.inl u : V ⊕ V) ∈ ({Sum.inl v} : Finset (V ⊕ V)) ↔
          (Sum.inr u : V ⊕ V) ∈ ({Sum.inl v} : Finset (V ⊕ V)))) = {v} := by ext u; simp
      rw [hA, hB, hC, cutEdges_empty]
      simp [dvec]
    · have hA : (univ.filter fun u => (Sum.inl u : V ⊕ V) ∈ ({Sum.inr v} : Finset (V ⊕ V))) =
          ∅ := by ext u; simp
      have hB : (univ.filter fun u => (Sum.inr u : V ⊕ V) ∈ ({Sum.inr v} : Finset (V ⊕ V))) =
          {v} := by ext u; simp
      have hC : (univ.filter fun u => ¬ ((Sum.inl u : V ⊕ V) ∈ ({Sum.inr v} : Finset (V ⊕ V)) ↔
          (Sum.inr u : V ⊕ V) ∈ ({Sum.inr v} : Finset (V ⊕ V)))) = {v} := by ext u; simp
      rw [hA, hB, hC, cutEdges_empty]
      simp [dvec]
  · rw [sum_gcut_dEnds]
    set A := univ.filter fun v => (Sum.inl v : V ⊕ V) ∈ T with hA
    set B := univ.filter fun v => (Sum.inr v : V ⊕ V) ∈ T with hB
    have hTAB : T = A.disjSum B := by
      ext t; rcases t with v | v <;> simp [hA, hB]
    have hcard : T.card = A.card + B.card := by rw [hTAB, Finset.card_disjSum]
    have hfil : (univ.filter fun v => ¬ ((Sum.inl v : V ⊕ V) ∈ T ↔ (Sum.inr v : V ⊕ V) ∈ T)) =
        univ.filter (fun v => ¬ (v ∈ A ↔ v ∈ B)) := by
      ext v; simp [hA, hB]
    rw [hfil]
    simp only [dvec]
    have e1 := Finset.card_sdiff_add_card_inter A B
    have e2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at e2
    rcases Nat.even_or_odd (A \ B).card with hev | hodd
    · have hodd' : Odd (B \ A).card := by
        obtain ⟨k, hk⟩ := hT
        obtain ⟨j, hj⟩ := hev
        exact ⟨k - j - (A ∩ B).card, by omega⟩
      have := lower_bound G hx B A hodd'
      have hfil' : (univ.filter fun v => ¬ (v ∈ B ↔ v ∈ A)) =
          univ.filter (fun v => ¬ (v ∈ A ↔ v ∈ B)) := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      rw [hfil'] at this
      linarith
    · exact lower_bound G hx A B hodd
end MatchingPolytope
