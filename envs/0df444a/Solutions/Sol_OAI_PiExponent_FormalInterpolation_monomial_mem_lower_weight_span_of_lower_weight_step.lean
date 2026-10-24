-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomial_mem_lower_weight_span_of_lower_weight_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:37:13.437238+00:00
-- url     : https://prove2.me/submissions/6b8d8153-2b26-4ac6-b99c-6eb51a6740e1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_mul_lower_weight_span

open scoped BigOperators

theorem solution {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ))
    (W : Fin d → Nat) (n : Fin d → Nat)
    (hred : ∀ i : Fin d,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈
        Submodule.span A {f : MvPolynomial (Fin d) ℂ |
          ∃ a : Fin d →₀ Nat,
            (∑ k : Fin d, a k * W k) < n i * W i ∧
              f = MvPolynomial.monomial a (1 : ℂ)})
    (e : Fin d →₀ Nat) (hover : ∃ i : Fin d, n i ≤ e i) :
    MvPolynomial.monomial e (1 : ℂ) ∈
      Submodule.span A {f : MvPolynomial (Fin d) ℂ |
        ∃ b : Fin d →₀ Nat,
          (∑ k : Fin d, b k * W k) < (∑ k : Fin d, e k * W k) ∧
            f = MvPolynomial.monomial b (1 : ℂ)} := by
  classical
  obtain ⟨i, hi⟩ := hover
  let c : Fin d →₀ Nat := e - Finsupp.single i (n i)
  have he : c + Finsupp.single i (n i) = e := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [c, Nat.sub_add_cancel hi]
    · simp [c, hk]
  have hpow := hred i
  rw [MvPolynomial.X_pow_eq_monomial] at hpow
  have hmul := OAI.PiExponent.FormalInterpolation.monomial_mul_lower_weight_span
    A W c (n i * W i) (MvPolynomial.monomial (Finsupp.single i (n i)) (1 : ℂ)) hpow
  have hweight : (∑ k : Fin d, c k * W k) + n i * W i =
      ∑ k : Fin d, e k * W k := by
    rw [← he]
    simp_rw [Finsupp.add_apply, add_mul]
    rw [Finset.sum_add_distrib]
    simp [Finsupp.single_apply]
  have hmon : MvPolynomial.monomial c (1 : ℂ) *
      MvPolynomial.monomial (Finsupp.single i (n i)) (1 : ℂ) =
      MvPolynomial.monomial e (1 : ℂ) := by
    rw [MvPolynomial.monomial_mul, mul_one, ← he]
  rw [← hweight, ← hmon]
  exact hmul