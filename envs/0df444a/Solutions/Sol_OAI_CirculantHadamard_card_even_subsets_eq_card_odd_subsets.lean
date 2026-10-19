-- Prove2me | solution 1 for OAI.CirculantHadamard.card_even_subsets_eq_card_odd_subsets
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:02:28.233106+00:00
-- url     : https://prove2.me/submissions/d59199bb-06a0-4392-ae63-40e6d2a08923

import Mathlib

theorem solution {I : Type*} (t : Finset I) (ht : t.Nonempty) :
    (t.powerset.filter (fun S => Even S.card)).card =
      (t.powerset.filter (fun S => Odd S.card)).card := by
  classical
  have h := Finset.sum_powerset_neg_one_pow_card_of_nonempty ht
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun S => Even S.card)] at h
  have h1 : ∑ S ∈ t.powerset.filter (fun S => Even S.card), (-1 : ℤ) ^ S.card =
      ((t.powerset.filter (fun S => Even S.card)).card : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [(Finset.mem_filter.1 hS).2.neg_one_pow]; simp
  have h2 : ∑ S ∈ t.powerset.filter (fun S => ¬ Even S.card), (-1 : ℤ) ^ S.card =
      -((t.powerset.filter (fun S => Odd S.card)).card : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
    simp_rw [Nat.not_even_iff_odd]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [(Finset.mem_filter.1 hS).2.neg_one_pow]; simp
  rw [h1, h2] at h
  omega
