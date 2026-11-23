-- Prove2me | solution 1 for IncApproxVC.Oblivious.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T05:01:44.900904+00:00
-- url     : https://prove2.me/submissions/e207f94e-35cc-4222-9bb9-2f3a76fdf6d6

import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_Cuts

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : IncApproxVC.Oblivious.Digraph V) (_hG : G.Loopless)
    (S : Finset (V × Bool)) :
    (G.outNbhd (Finset.univ.filter fun v =>
        IncApproxVC.Oblivious.Digraph.minus v ∈ S ∧
        IncApproxVC.Oblivious.Digraph.plus v ∈ S)).card ≤
      (G.split.outBoundary S).card := by
  let minus := @IncApproxVC.Oblivious.Digraph.minus V
  let plus := @IncApproxVC.Oblivious.Digraph.plus V
  set L : Finset V := Finset.univ.filter fun v => minus v ∈ S ∧ plus v ∈ S
  have hsub : G.outNbhd L ⊆ (G.split.outBoundary S).image (fun e => e.2.1) := by
    intro w hw
    unfold IncApproxVC.Oblivious.Digraph.outNbhd IncApproxVC.Oblivious.Digraph.outBoundary
      IncApproxVC.Oblivious.Digraph.edgesBetween at hw
    rcases Finset.mem_image.mp hw with ⟨⟨u, w'⟩, he, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_compl] at he
    rcases he with ⟨heG, huL, hwL⟩
    have hu_plus : plus u ∈ S := (Finset.mem_filter.mp huL).2.2
    by_cases hw_minus : minus w' ∈ S
    · have hw_plus : plus w' ∉ S := fun hp =>
        hwL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_minus, hp⟩)
      refine Finset.mem_image.mpr ⟨(minus w', plus w'), ?_, rfl⟩
      unfold IncApproxVC.Oblivious.Digraph.split IncApproxVC.Oblivious.Digraph.outBoundary
        IncApproxVC.Oblivious.Digraph.edgesBetween
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_compl]
      exact ⟨Or.inl ⟨w', rfl⟩, hw_minus, hw_plus⟩
    · refine Finset.mem_image.mpr ⟨(plus u, minus w'), ?_, rfl⟩
      unfold IncApproxVC.Oblivious.Digraph.split IncApproxVC.Oblivious.Digraph.outBoundary
        IncApproxVC.Oblivious.Digraph.edgesBetween
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_compl]
      exact ⟨Or.inr ⟨(u, w'), heG, rfl⟩, hu_plus, hw_minus⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le
