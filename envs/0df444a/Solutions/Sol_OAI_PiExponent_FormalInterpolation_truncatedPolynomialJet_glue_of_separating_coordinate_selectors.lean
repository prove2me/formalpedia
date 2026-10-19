-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_glue_of_separating_coordinate_selectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:50:12.040807+00:00
-- url     : https://prove2.me/submissions/cc520ecd-a67f-4a36-98b1-1e4782163798

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation
theorem h41_coeff_mul_box {n : Nat} (A B : MvPolynomial (Fin n) Complex) (d : Fin n →₀ ℕ)
    (ε : Complex) (hA : ∀ b ≤ d, A.coeff b = if b = 0 then ε else 0) :
    (A * B).coeff d = ε * B.coeff d := by
  classical
  rw [MvPolynomial.coeff_mul]
  rw [Finset.sum_eq_single (0, d)]
  · rw [hA 0 zero_le, if_pos rfl]
  · intro x hx hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hle : x.1 ≤ d := by rw [← hx]; exact le_self_add
    rw [hA x.1 hle]
    by_cases h0 : x.1 = 0
    · exfalso; apply hne
      have : x.2 = d := by rw [← hx, h0, zero_add]
      ext <;> simp [h0, this]
    · simp [h0]
  · intro h; exfalso; apply h; rw [Finset.HasAntidiagonal.mem_antidiagonal, zero_add]

theorem solution
    {m : Nat} (K : Nat) (T : Fin m → Nat)
    (c : Fin K → Fin m → Complex)
    (S : Fin (m + 1) → Nat)
    (Q : Fin K → MvPolynomial (Fin (m + 1)) Complex)
    (E : Fin K → MvPolynomial (Fin (m + 1)) Complex)
    (hsel : ∀ (j k : Fin K)
      (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
      (truncatedPolynomialJet (c j) T (E k)).coeff
          (InterpolationMatrix.exponentVector a.1) =
        if j = k ∧ a.1 = 0 then 1 else 0) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      ∀ (j : Fin K)
        (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
        (truncatedPolynomialJet (c j) T P).coeff
            (InterpolationMatrix.exponentVector a.1) =
          (truncatedPolynomialJet (c j) T (Q j)).coeff
            (InterpolationMatrix.exponentVector a.1) := by
  classical
  refine ⟨∑ k, E k * Q k, ?_⟩
  intro j a
  rw [map_sum, MvPolynomial.coeff_sum]
  simp only [map_mul]
  rw [Finset.sum_eq_single j]
  · rw [h41_coeff_mul_box _ _ _ 1, one_mul]
    intro b hb
    have hbS : ∀ i, (⇑b) i < S i := fun i => lt_of_le_of_lt (hb i) (by
      have := a.2 i; simpa [InterpolationMatrix.exponentVector] using this)
    have := hsel j j ⟨⇑b, hbS⟩
    simp only [InterpolationMatrix.exponentVector, Finsupp.equivFunOnFinite_symm_coe] at this
    rw [this]
    simp
  · intro k _ hkj
    rw [h41_coeff_mul_box _ _ _ 0, zero_mul]
    intro b hb
    have hbS : ∀ i, (⇑b) i < S i := fun i => lt_of_le_of_lt (hb i) (by
      have := a.2 i; simpa [InterpolationMatrix.exponentVector] using this)
    have := hsel j k ⟨⇑b, hbS⟩
    simp only [InterpolationMatrix.exponentVector, Finsupp.equivFunOnFinite_symm_coe] at this
    rw [this]
    simp [Ne.symm hkj]
  · intro h; exact absurd (Finset.mem_univ j) h

