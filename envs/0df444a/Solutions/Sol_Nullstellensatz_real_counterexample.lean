-- Prove2me | solution 1 for Nullstellensatz.real_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:16:52.975345+00:00
-- url     : https://prove2.me/submissions/03687730-7451-4d26-b6d7-2ce6ae725074

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

theorem solution :
    Ideal.span {(Polynomial.X ^ 2 + 1 : Polynomial ℝ)} ≠ ⊤ ∧
      ¬ ∃ x : ℝ, ∀ f ∈ Ideal.span {(Polynomial.X ^ 2 + 1 : Polynomial ℝ)}, f.eval x = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    have hd := Polynomial.degree_eq_zero_of_isUnit h
    have h2 : (Polynomial.X ^ 2 + 1 : Polynomial ℝ) = Polynomial.X ^ 2 + Polynomial.C 1 := by simp
    rw [h2, Polynomial.degree_X_pow_add_C (by norm_num)] at hd
    exact absurd hd (by decide)
  · rintro ⟨x, hx⟩
    have := hx (Polynomial.X ^ 2 + 1) (Ideal.subset_span rfl)
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at this
    nlinarith [sq_nonneg x]
