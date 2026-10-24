-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_monomial_coeff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:18:28.425912+00:00
-- url     : https://prove2.me/submissions/892c960e-0772-4aa8-98f8-6e192c425c22

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (N : Nat)
    (hbelow : ∀ d e : Fin n → Nat,
      (∑ k, d k) ≤ N → (∑ k, e k) ≤ N →
      (∑ k, e k) < (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) = 0)
    (hsame : ∀ d e : Fin n → Nat,
      (∑ k, d k) ≤ N → (∑ k, e k) ≤ N →
      (∑ k, e k) = (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) =
            (if d = e then 1 else 0))
    (c : Complex)
    (d e : Fin n → Nat)
    (hd : (∑ k, d k) ≤ N)
    (he : (∑ k, e k) ≤ N)
    (hle : (∑ k, e k) ≤ (∑ k, d k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) c)) =
      (if d = e then c else 0) := by
  have hm : MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) c =
      c • MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul]
  rcases lt_or_eq_of_le hle with h | h
  · rw [hbelow d e hd he h, smul_zero]
    have : d ≠ e := by rintro rfl; exact lt_irrefl _ h
    simp [this]
  · rw [hsame d e hd he h]
    split_ifs <;> simp
