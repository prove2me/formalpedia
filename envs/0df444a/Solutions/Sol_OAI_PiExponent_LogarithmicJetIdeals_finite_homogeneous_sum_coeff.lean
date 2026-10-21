-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_homogeneous_sum_coeff
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T15:49:43.485073+00:00
-- url     : https://prove2.me/submissions/746ddc5f-288d-41ce-a8d4-bd48ce495dde

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
    (value : (Fin n → Nat) → Complex)
    (m : Nat)
    (hm : m ≤ N)
    (S : Finset (Fin n → Nat))
    (hS : ∀ d : Fin n → Nat, d ∈ S ↔ (∑ k, d k) = m)
    (e : Fin n → Nat)
    (he : (∑ k, e k) ≤ m) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi
        (∑ d ∈ S,
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (value d))) =
      (if (∑ k, e k) = m then value e else 0) := by
  classical
  have hscale (d : Fin n → Nat) (c : Complex) :
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) c)) =
      c * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) := by
    have hmono :
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) c =
        c • MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hmono, map_smul, MvPowerSeries.coeff_smul]
  have heN : (∑ k, e k) ≤ N := le_trans he hm
  have hterm : ∀ d ∈ S,
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (value d))) =
      (if d = e then value d else 0) := by
    intro d hd
    have hdeg : (∑ k, d k) = m := (hS d).1 hd
    have hdN : (∑ k, d k) ≤ N := by rw [hdeg]; exact hm
    have hle : (∑ k, e k) ≤ (∑ k, d k) := by rw [hdeg]; exact he
    rw [hscale]
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hne : d ≠ e := by
        intro h
        subst d
        exact (lt_irrefl _ hlt)
      rw [hbelow d e hdN heN hlt]
      simp only [hne, if_false, mul_zero]
    · rw [hsame d e hdN heN heq]
      by_cases hde : d = e <;> simp only [hde, if_true, if_false, mul_one, mul_zero]
  calc
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (∑ d ∈ S,
            MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (value d))) =
        ∑ d ∈ S, MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (value d))) := by
      simp only [map_sum]
    _ = ∑ d ∈ S, (if d = e then value d else 0) :=
      Finset.sum_congr rfl hterm
    _ = (if (∑ k, e k) = m then value e else 0) := by
      rw [Finset.sum_ite_eq']
      by_cases hmem : e ∈ S
      · rw [if_pos hmem, if_pos ((hS e).1 hmem)]
      · rw [if_neg hmem, if_neg (fun hdeg => hmem ((hS e).2 hdeg))]
