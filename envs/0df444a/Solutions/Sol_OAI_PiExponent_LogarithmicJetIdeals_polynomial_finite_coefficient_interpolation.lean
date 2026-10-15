-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.polynomial_finite_coefficient_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:40:11.890987+00:00
-- url     : https://prove2.me/submissions/58e88a2e-133b-4a52-8bc5-c63d828b9273

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {Alpha : Type} [Fintype Alpha] [DecidableEq Alpha] {m : Nat}
    (degree : Alpha → Fin (m + 1) → Nat)
    (hdegree : Function.Injective degree) (value : Alpha → Complex) :
    ∃ R : MvPolynomial (Fin (m + 1)) Complex,
      ∀ b : Alpha,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (MvPolynomial.toMvPowerSeries R) = value b := by
  classical
  let exponent : Alpha → (Fin (m + 1) →₀ Nat) :=
    fun b => Finsupp.equivFunOnFinite.symm (degree b)
  refine ⟨∑ a : Alpha, MvPolynomial.monomial (exponent a) (value a), ?_⟩
  intro b
  change MvPolynomial.coeff (exponent b)
    (∑ a : Alpha, MvPolynomial.monomial (exponent a) (value a)) = value b
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single b]
  · simp [exponent, MvPolynomial.coeff_monomial]
  · intro c hc hcb
    have hne : exponent c ≠ exponent b := by
      intro he
      apply hcb
      apply hdegree
      exact Finsupp.equivFunOnFinite.symm.injective he
    simp [MvPolynomial.coeff_monomial, hne]
  · simp