-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_class_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:49:40.290993+00:00
-- url     : https://prove2.me/submissions/85f41c4c-026a-4a10-80e4-189640458987

import Mathlib
open scoped BigOperators

theorem solution (d : Nat) (N : Fin d → Nat) (hN : ∀ i, 0 < N i) (i : Fin d) : IsIntegral ℂ (Ideal.Quotient.mk (Ideal.span (Set.range (fun j : Fin d => (MvPolynomial.X j : MvPolynomial (Fin d) ℂ) ^ N j))) (MvPolynomial.X i)) := by
  refine ⟨Polynomial.X ^ N i, Polynomial.monic_X_pow _, ?_⟩
  rw [Polynomial.eval₂_X_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩
