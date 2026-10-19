-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_product_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:04:20.761807+00:00
-- url     : https://prove2.me/submissions/a3bfb976-2e76-4866-981f-0e2faf2beed1

import Mathlib
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
theorem solution
    {m : Nat}
    (N : Nat)
    (R : Fin (m + 1) → MvPolynomial (Fin (m + 1)) Complex)
    (hR : ∀ i : Fin (m + 1), ∀ b ∈ (R i).support,
      b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) :
    ∀ b ∈ (∏ i : Fin (m + 1), R i).support,
      ∀ i : Fin (m + 1), b i < N := by
  classical
  have key : ∀ S : Finset (Fin (m + 1)), ∀ b ∈ (∏ i ∈ S, R i).support,
      ∀ i : Fin (m + 1), (i ∈ S → b i < N) ∧ (i ∉ S → b i = 0) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro b hb i
      rw [Finset.prod_empty, MvPolynomial.support_one] at hb
      simp only [Finset.mem_singleton] at hb
      subst hb
      simp
    | insert j S hj ih =>
      intro b hb i
      rw [Finset.prod_insert hj] at hb
      have hb' := MvPolynomial.support_mul _ _ hb
      obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Finset.mem_add.mp hb'
      have h1 := hR j b1 hb1
      have h2 := ih b2 hb2
      simp only [Finsupp.add_apply, Finset.mem_insert]
      by_cases hij : i = j
      · subst hij
        have := (h2 i).2 hj
        exact ⟨fun _ => by rw [this, add_zero]; exact h1.1, fun h => absurd (Or.inl rfl) h⟩
      · have hb1i : b1 i = 0 := h1.2 i hij
        rw [hb1i, zero_add]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases h with h | h
          · exact absurd h hij
          · exact (h2 i).1 h
        · exact (h2 i).2 (fun h' => h (Or.inr h'))
  intro b hb i
  exact (key Finset.univ b hb i).1 (Finset.mem_univ i)
