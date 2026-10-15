-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients_of_terms
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:34:04.002269+00:00
-- url     : https://prove2.me/submissions/1f757bce-668a-4f9e-ab34-dfbc34645d96

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (P : MvPolynomial (Fin n) Complex)
    (D : Nat)
    (e : Fin n → Nat)
    (hhom : ∀ m ∈ P.support, (∑ i, m i) = D)
    (hterm : ∀ m ∈ P.support,
      ((∑ i, e i) < D →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi
            (MvPolynomial.monomial m (MvPolynomial.coeff m P))) = 0) ∧
      ((∑ i, e i) = D →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi
            (MvPolynomial.monomial m (MvPolynomial.coeff m P))) =
              MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
                (MvPolynomial.monomial m (MvPolynomial.coeff m P)))) :
    ((∑ i, e i) < D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi P) = 0) ∧
    ((∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi P) =
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) P) := by
  classical
  let idx := Finsupp.equivFunOnFinite.symm e
  let term (m : Fin n →₀ Nat) :=
    MvPolynomial.monomial m (MvPolynomial.coeff m P)
  have hpoly : P = ∑ m ∈ P.support, term m := by
    simpa [term] using (MvPolynomial.as_sum P)
  have heval : MvPolynomial.aeval phi P =
      ∑ m ∈ P.support, MvPolynomial.aeval phi (term m) := by
    calc
      MvPolynomial.aeval phi P =
          MvPolynomial.aeval phi (∑ m ∈ P.support, term m) :=
        congrArg (MvPolynomial.aeval phi) hpoly
      _ = ∑ m ∈ P.support, MvPolynomial.aeval phi (term m) := by
        simp only [map_sum]
  have hcoeff : MvPowerSeries.coeff idx (MvPolynomial.aeval phi P) =
      ∑ m ∈ P.support,
        MvPowerSeries.coeff idx (MvPolynomial.aeval phi (term m)) := by
    rw [heval]
    simp only [map_sum]
  have hpc : MvPolynomial.coeff idx P =
      ∑ m ∈ P.support, MvPolynomial.coeff idx (term m) := by
    calc
      MvPolynomial.coeff idx P =
          MvPolynomial.coeff idx (∑ m ∈ P.support, term m) :=
        congrArg (MvPolynomial.coeff idx) hpoly
      _ = ∑ m ∈ P.support, MvPolynomial.coeff idx (term m) := by
        rw [MvPolynomial.coeff_sum]
  constructor
  · intro hlt
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro m hm
    exact (hterm m hm).1 hlt
  · intro heq
    rw [hcoeff, hpc]
    apply Finset.sum_congr rfl
    intro m hm
    exact (hterm m hm).2 heq