-- Prove2me | solution 1 for InverseZeroSum.Candidate3.weighted_sum_plus_singleton_eq_double
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:40:27.77628+00:00
-- url     : https://prove2.me/submissions/30220e84-f731-4c86-ab14-0d189462721d

import Mathlib


theorem solution {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (A : Finset α) (f : α → M) (w : α → ℕ)
    {u : α} (hu : u ∈ A) (huOne : w u = 1)
    (hOther : ∀ x ∈ A.erase u, w x = 2) :
    (∑ x ∈ A, w x • f x) + f u =
      ∑ x ∈ A, (2 : ℕ) • f x := by
  have ho : (∑ x ∈ A.erase u, w x • f x) = ∑ x ∈ A.erase u, (2:ℕ) • f x := by
    apply Finset.sum_congr rfl; intro x hx; rw [hOther x hx]
  rw [← Finset.sum_erase_add A (fun x => w x • f x) hu, ← Finset.sum_erase_add A (fun x => (2:ℕ) • f x) hu, ho,huOne,one_smul,two_nsmul,add_assoc]
