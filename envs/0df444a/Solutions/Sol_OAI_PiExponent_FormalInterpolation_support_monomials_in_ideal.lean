-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_monomials_in_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:52:31.202004+00:00
-- url     : https://prove2.me/submissions/83ecb025-6ab4-412c-b464-3179431f408f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem solution {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ))
    (f : MvPolynomial (Fin d) ℂ)
    (hterms : ∀ e ∈ f.support,
      MvPolynomial.monomial e (f.coeff e) ∈ I) :
    f ∈ I := by
  rw [MvPolynomial.as_sum f]
  exact I.sum_mem fun e he => hterms e he