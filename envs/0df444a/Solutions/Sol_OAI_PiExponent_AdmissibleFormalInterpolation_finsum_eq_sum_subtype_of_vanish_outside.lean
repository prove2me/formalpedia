-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.finsum_eq_sum_subtype_of_vanish_outside
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:44:11.783987+00:00
-- url     : https://prove2.me/submissions/c6f79592-4eb6-4307-ae86-16c8ff9071ea

import Mathlib

open scoped BigOperators
theorem solution
    {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℂ)
    (hf : ∀ x, x ∉ s → f x = 0) :
    (∑ᶠ x, f x) = ∑ x : ↥s, f x := by
  rw [finsum_eq_sum_of_support_subset f (s := s) (by
    intro x hx
    by_contra h
    exact hx (hf x h))]
  exact (Finset.sum_coe_sort s f).symm
