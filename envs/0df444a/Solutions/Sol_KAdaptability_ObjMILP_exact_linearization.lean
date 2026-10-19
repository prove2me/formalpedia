-- Prove2me | solution 1 for KAdaptability.ObjMILP.exact_linearization
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:26:11.894142+00:00
-- url     : https://prove2.me/submissions/ef24ea33-f350-48e3-ab58-708c6e4e51d4

import Mathlib
set_option autoImplicit false

theorem solution {M : ℕ} (y z : Fin M → ℝ) (β : ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hz : 0 ≤ z) :
    z = β • y ↔
      (z ≤ y ∧ z ≤ β • (1 : Fin M → ℝ) ∧ (β - 1) • (1 : Fin M → ℝ) + y ≤ z) := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩ <;> intro i <;> rcases hy i with h | h <;>
      simp [h] <;> linarith
  · rintro ⟨h1, h2, h3⟩
    funext i
    have a := h1 i
    have b := h2 i
    have c := h3 i
    have d := hz i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, Pi.zero_apply, smul_eq_mul, mul_one] at a b c d ⊢
    rcases hy i with h | h <;> rw [h] at a c ⊢ <;> linarith
