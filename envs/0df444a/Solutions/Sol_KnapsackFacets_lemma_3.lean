-- Prove2me | solution 1 for KnapsackFacets.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:22:26.329359+00:00
-- url     : https://prove2.me/submissions/79702b79-d0bb-4234-a3b1-2189011a92cb

import Mathlib
import Definitions.Def_KnapsackFacets_ShiftedFib

set_option autoImplicit false

namespace Aux_KFl3

open KnapsackFacets

theorem step (N : ℕ) : shiftedFib (N + 1) ≤ 1 + ∑ i ∈ Finset.Icc 1 N, shiftedFib i := by
  rcases N with _ | _ | _ | N
  · simp [shiftedFib]
  · simp [shiftedFib]
  · simp [shiftedFib]
  · show shiftedFib (N + 4) ≤ 1 + ∑ i ∈ Finset.Icc 1 (N + 3), shiftedFib i
    have h : ({N + 2, N + 3} : Finset ℕ) ⊆ Finset.Icc 1 (N + 3) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      omega
    have := Finset.sum_le_sum_of_subset (f := shiftedFib) h
    rw [Finset.sum_pair (by omega)] at this
    have e : shiftedFib (N + 4) = shiftedFib (N + 2) + shiftedFib (N + 3) := rfl
    rw [e]
    omega

theorem main (N : ℕ) : ∀ τ, τ ≤ ∑ i ∈ Finset.Icc 1 N, shiftedFib i →
    ∃ S ⊆ Finset.Icc 1 N, ∑ i ∈ S, shiftedFib i = τ := by
  induction N with
  | zero =>
    intro τ hτ
    simp at hτ
    exact ⟨∅, Finset.empty_subset _, by simp [hτ]⟩
  | succ N ih =>
    intro τ hτ
    rw [Finset.sum_Icc_succ_top (by omega)] at hτ
    have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 (N + 1) := Finset.Icc_subset_Icc le_rfl (by omega)
    by_cases h : τ ≤ ∑ i ∈ Finset.Icc 1 N, shiftedFib i
    · obtain ⟨S, hS, hsum⟩ := ih τ h
      exact ⟨S, hS.trans hsub, hsum⟩
    · have hst := step N
      obtain ⟨S, hS, hsum⟩ := ih (τ - shiftedFib (N + 1)) (by omega)
      have hnot : N + 1 ∉ S := fun hm => by
        have := hS hm; simp at this
      refine ⟨insert (N + 1) S, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · simp
        · exact hsub (hS hx)
      · rw [Finset.sum_insert hnot, hsum]
        omega

end Aux_KFl3

open KnapsackFacets Aux_KFl3 in
theorem solution (r : ℕ) (hr : 1 ≤ r) (τ : ℕ)
    (hτ : τ ≤ ∑ i ∈ Finset.Icc 1 (2 * r + 1), shiftedFib i) :
    ∃ S ⊆ Finset.Icc 1 (2 * r + 1), ∑ i ∈ S, shiftedFib i = τ :=
  main (2 * r + 1) τ hτ
