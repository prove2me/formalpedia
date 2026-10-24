-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_translated_polynomial_coefficients_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:44:43.059418+00:00
-- url     : https://prove2.me/submissions/ffeee268-38ac-42de-b7bc-e5ea13ea63c9

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_translated_polynomial_full_jets_interpolate

open MvPolynomial

theorem solution
    {n : Nat} {J A : Type} [Fintype J] [Fintype A]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (e : A → (Fin n →₀ Nat)) (he : Function.Injective e)
    (y : J × A → Complex) :
    ∃ Q : MvPolynomial (Fin n) Complex, ∀ (j : J) (a : A),
      (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.C (c j i) + MvPolynomial.X i) Q).coeff
          (e a) = y (j, a) := by
  classical
  let D : Nat := ∑ a : A, ∑ i : Fin n, e a i
  let z : J → (Fin n →₀ Nat) → Complex := fun j α =>
    if h : ∃ a : A, e a = α then y (j, Classical.choose h) else 0
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_translated_polynomial_full_jets_interpolate
      c hc D z
  refine ⟨Q, ?_⟩
  intro j a
  have hdeg : (∑ i : Fin n, e a i) ≤ D := by
    dsimp [D]
    exact Finset.single_le_sum
      (fun b _ => Nat.zero_le (∑ i : Fin n, e b i))
      (Finset.mem_univ a)
  have hex : ∃ b : A, e b = e a := ⟨a, rfl⟩
  have hchoose : Classical.choose hex = a := he (Classical.choose_spec hex)
  have h := hQ j (e a) hdeg
  simpa [z, hex, hchoose] using h