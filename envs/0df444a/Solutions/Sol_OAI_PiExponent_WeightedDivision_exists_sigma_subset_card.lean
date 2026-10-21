-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.exists_sigma_subset_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:44:30.140091+00:00
-- url     : https://prove2.me/submissions/fdadd4b1-cdd2-4cd1-a650-68e557888435

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (s : ℕ)
    (hs : s ≤ ∑ i, q i) :
    ∃ t : Finset (Σ i, Fin (q i)), t.card = s := by
  classical
  have hcard : s ≤ (Finset.univ : Finset (Σ i, Fin (q i))).card := by
    simpa using hs
  obtain ⟨t, _ht, ht⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨t, ht⟩