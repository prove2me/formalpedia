-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_as_sum
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T15:48:21.677915+00:00
-- url     : https://prove2.me/submissions/053c846c-827b-4b67-ac7b-cb32dcbbf092

import Mathlib.Algebra.MvPolynomial.Basic

open scoped BigOperators

theorem solution
    {σ : Type} [DecidableEq σ] {R : Type} [CommSemiring R]
    (p : MvPolynomial σ R) (i : σ)
    (hsupport : ∀ (s : σ →₀ ℕ), p.coeff s ≠ 0 →
      ∀ j : σ, s j ≠ 0 → j = i) :
    p = ∑ n ∈ p.support.image (fun s => s i),
      MvPolynomial.monomial (Finsupp.single i n)
        (p.coeff (Finsupp.single i n)) := by
  classical
  have hsingle : ∀ s ∈ p.support, s = Finsupp.single i (s i) := by
    intro s hs
    have hcoeff : p.coeff s ≠ 0 := by
      rwa [MvPolynomial.mem_support_iff] at hs
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · have hz : s j = 0 := by
        by_contra hne
        exact hj (hsupport s hcoeff j hne)
      rw [hz, Finsupp.single_eq_of_ne' (Ne.symm hj)]
  trans ∑ v ∈ p.support, MvPolynomial.monomial v (p.coeff v)
  · exact MvPolynomial.as_sum p
  have hinj : Set.InjOn (fun s : σ →₀ ℕ => s i) ↑p.support := by
    intro s hs t ht hst
    rw [hsingle s hs, hsingle t ht]
    exact congrArg (Finsupp.single i) hst
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl ?_
  intro s hs
  have h := hsingle s hs
  conv_lhs => rw [h]
