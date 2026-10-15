-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.degree_m_correction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:33:45.749813+00:00
-- url     : https://prove2.me/submissions/99e03905-60f2-4836-aa77-4d611898051a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_degree_m_homogeneous_surjectivity
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_add

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
    (Q : MvPolynomial (Fin n) Complex)
    (hm : m ≤ N) :
    ∃ R : MvPolynomial (Fin n) Complex,
      (∀ e : Fin n → Nat, (∑ k, e k) < m →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi (Q + R)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi Q)) ∧
      (∀ e : Fin n → Nat, (∑ k, e k) = m →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi (Q + R)) = value e) := by
  let residual : (Fin n → Nat) → Complex := fun e =>
    value e - MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi Q)
  obtain ⟨R, hlow, hdegree⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.degree_m_homogeneous_surjectivity
      phi N hbelow hsame residual m hm
  refine ⟨R, ?_, ?_⟩
  · intro e he
    calc
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi (Q + R)) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.aeval phi Q) +
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.aeval phi R) :=
        OAI.PiExponent.LogarithmicJetIdeals.coeff_add phi Q R e
      _ = MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.aeval phi Q) := by rw [hlow e he]; simp
  · intro e he
    calc
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi (Q + R)) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.aeval phi Q) +
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.aeval phi R) :=
        OAI.PiExponent.LogarithmicJetIdeals.coeff_add phi Q R e
      _ = value e := by
        rw [hdegree e he]
        dsimp [residual]
        exact (by
          calc
            MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
                (MvPolynomial.aeval phi Q) +
                (value e - MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
                  (MvPolynomial.aeval phi Q)) =
              MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
                (MvPolynomial.aeval phi Q) + value e -
                MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
                  (MvPolynomial.aeval phi Q) := by rw [← add_sub_assoc]
            _ = value e := add_sub_cancel_left _ _)