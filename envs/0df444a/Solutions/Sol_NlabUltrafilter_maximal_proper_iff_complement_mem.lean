-- Prove2me | solution 1 for NlabUltrafilter.maximal_proper_iff_complement_mem
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T08:52:52.888131+00:00
-- url     : https://prove2.me/submissions/36ec0f05-206c-4c9b-b84b-5b1290832bb4

import Mathlib

theorem solution {α : Type*} (F : Filter α) :
    (F.NeBot ∧ ∀ G : Filter α, G.NeBot → G ≤ F → F ≤ G) ↔
      (F.NeBot ∧ ∀ s : Set α, s ∈ F ∨ sᶜ ∈ F) := by
  constructor
  · rintro ⟨hF, hmax⟩
    refine ⟨hF, fun s => ?_⟩
    by_contra hns
    rw [not_or] at hns
    obtain ⟨hs, hsc⟩ := hns
    have hG : (F ⊓ Filter.principal s).NeBot := by
      rw [Filter.inf_principal_neBot_iff]
      intro U hU
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      apply hsc
      refine Filter.mem_of_superset hU ?_
      intro x hx hxs
      have : x ∈ U ∩ s := ⟨hx, hxs⟩
      rw [hne] at this
      exact this
    have hle := hmax _ hG inf_le_left
    exact hs (hle (Filter.mem_inf_of_right (Filter.mem_principal_self s)))
  · rintro ⟨hF, hcomp⟩
    refine ⟨hF, fun G hG hGF s hs => ?_⟩
    rcases hcomp s with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx1, hx2⟩ := Filter.nonempty_of_mem (Filter.inter_mem hs (hGF h))
      exact hx2 hx1
