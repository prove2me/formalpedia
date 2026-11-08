-- Prove2me | solution 1 for KnapsackFacets.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:00:56.128414+00:00
-- url     : https://prove2.me/submissions/cd27fc7b-15fe-4b42-9137-6d9829ac4b9c

import Definitions.Def_KnapsackFacets_ShiftedFib

set_option autoImplicit false

open KnapsackFacets in
theorem solution (j : ℕ) (hj : 3 ≤ j) :
    KnapsackFacets.shiftedFib j = ∑ i ∈ Finset.Icc 1 (j - 2), KnapsackFacets.shiftedFib i := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 3 := ⟨k - 3, by omega⟩
    have e : i + 3 - 2 = i + 1 := by omega
    rw [e] at ih
    have e2 : i + 3 + 1 - 2 = i + 1 + 1 := by omega
    rw [e2, Finset.sum_Icc_succ_top (by omega), ← ih]
    have hrec : KnapsackFacets.shiftedFib (i + 3 + 1) =
        KnapsackFacets.shiftedFib (i + 2) + KnapsackFacets.shiftedFib (i + 3) := by
      rw [KnapsackFacets.shiftedFib]
    have h22 : KnapsackFacets.shiftedFib (i + 1 + 1) = KnapsackFacets.shiftedFib (i + 2) := rfl
    rw [hrec, h22]
    omega
