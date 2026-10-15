-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.support_monomials_mem_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T22:19:27.130689+00:00
-- url     : https://prove2.me/submissions/8731879c-23ef-430a-898b-de3420051c17

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.BigOperators

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (h : ∀ d ∈ Q.support, MvPolynomial.monomial d (1 : ℂ) ∈ I) :
    Q ∈ I := by
  rw [MvPolynomial.as_sum Q]
  apply Ideal.sum_mem I
  intro d hd
  have hmul :
      MvPolynomial.C (MvPolynomial.coeff d Q) *
          MvPolynomial.monomial d (1 : ℂ) ∈ I :=
    I.mul_mem_left _ (h d hd)
  simpa [MvPolynomial.C_mul_monomial] using hmul