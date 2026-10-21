-- Prove2me | solution 2 for OAI.PiExponent.FinitePeriodCollision.coordinate_factor_support
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:12:11.745985+00:00
-- url     : https://prove2.me/submissions/c634bb23-41de-45f2-9004-60a35dc6beef

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Complex.Basic

open scoped BigOperators

theorem solution
    {m : ℕ} (a : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    ∀ (i : Fin m) (s : Fin m →₀ ℕ),
      ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff s ≠ 0 →
        ∀ j : Fin m, s j ≠ 0 → j = i := by
  intro i s hs j hj
  set p : MvPolynomial (Fin m) (PowerSeries ℂ) :=
    MvPolynomial.C (b i) + MvPolynomial.X i with hp_def
  -- The single factor `C (b i) + X i` lives on the coordinate axis through `i`.
  have hp : ∀ t : Fin m →₀ ℕ, p.coeff t ≠ 0 → ∀ j : Fin m, t j ≠ 0 → j = i := by
    intro t ht j hj
    by_contra hji
    apply ht
    have h0 : t ≠ 0 := by intro h; rw [h] at hj; simp at hj
    have hst : Finsupp.single i 1 ≠ t := by
      intro h
      have hz : (Finsupp.single i 1 : Fin m →₀ ℕ) j = 0 :=
        Finsupp.single_eq_of_ne' (Ne.symm hji)
      rw [h] at hz
      exact hj hz
    rw [hp_def, MvPolynomial.coeff_add, MvPolynomial.coeff_C, MvPolynomial.coeff_X,
      if_neg (Ne.symm h0), if_neg hst, add_zero]
  -- Every power keeps the support on the same coordinate axis.
  have key : ∀ n : ℕ, ∀ t : Fin m →₀ ℕ,
      (p ^ n).coeff t ≠ 0 → ∀ j : Fin m, t j ≠ 0 → j = i := by
    intro n
    induction n with
    | zero =>
      intro t ht j hj
      have h0 : t ≠ 0 := by intro h; rw [h] at hj; simp at hj
      have hz : (p ^ 0).coeff t = 0 := by
        rw [pow_zero, MvPolynomial.coeff_one, if_neg (Ne.symm h0)]
      exact absurd hz ht
    | succ n ih =>
      intro t ht j hj
      by_contra hji
      apply ht
      rw [pow_succ, MvPolynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      have hxmem : x.1 + x.2 = t := Finset.mem_antidiagonal.mp hx
      by_cases h1 : (p ^ n).coeff x.1 = 0
      · simp [h1]
      · by_cases h2 : p.coeff x.2 = 0
        · simp [h2]
        · exfalso
          have hxj1 : x.1 j = 0 := by
            by_contra hne
            exact hji (ih x.1 h1 j hne)
          have hxj2 : x.2 j = 0 := by
            by_contra hne
            exact hji (hp x.2 h2 j hne)
          have htj : t j = 0 := by
            rw [← hxmem, Finsupp.add_apply, hxj1, hxj2, add_zero]
          exact hj htj
  exact key (a i) s hs j hj
