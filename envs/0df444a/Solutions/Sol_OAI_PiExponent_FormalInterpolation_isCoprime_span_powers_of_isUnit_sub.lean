-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.isCoprime_span_powers_of_isUnit_sub
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:30:43.845323+00:00
-- url     : https://prove2.me/submissions/ba5aca8a-30cf-40be-9499-8ea7da30f8a1

import Mathlib.RingTheory.Ideal.Operations

theorem solution
    {R : Type} [CommRing R] {x y : R} (h : IsUnit (x - y)) (n p : Nat) :
    IsCoprime (Ideal.span ({x ^ n} : Set R)) (Ideal.span ({y ^ p} : Set R)) := by
  rw [Ideal.isCoprime_span_singleton_iff]
  apply IsCoprime.pow
  obtain ⟨u, hu⟩ := h
  refine ⟨(↑u⁻¹ : R), -(↑u⁻¹ : R), ?_⟩
  have : (↑u⁻¹ : R) * (x - y) = 1 := by rw [← hu]; exact u.inv_mul
  rw [← this]; ring
