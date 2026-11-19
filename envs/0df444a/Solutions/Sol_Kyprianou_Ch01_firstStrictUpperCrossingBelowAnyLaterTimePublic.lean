-- Prove2me | solution 1 for Kyprianou.Ch01.firstStrictUpperCrossingBelowAnyLaterTimePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:34:13.419292+00:00
-- url     : https://prove2.me/submissions/3745f313-2939-4e69-a2d7-6330ab4540a5

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (x : ℝ)
    (hcross : ∃ u : ℝ≥0, 0 < u ∧ x < f u)
    (t : ℝ≥0)
    (ht : sInf {u : ℝ≥0 | 0 < u ∧ x < f u} < t) :
    ∃ u : ℝ≥0, 0 < u ∧ x < f u ∧ u < t := by
  obtain ⟨v, hv0, hvx⟩ := hcross
  have hnonempty : ({u : ℝ≥0 | 0 < u ∧ x < f u} : Set ℝ≥0).Nonempty :=
    ⟨v, hv0, hvx⟩
  obtain ⟨u, hu, hut⟩ := exists_lt_of_csInf_lt hnonempty ht
  exact ⟨u, hu.1, hu.2, hut⟩
