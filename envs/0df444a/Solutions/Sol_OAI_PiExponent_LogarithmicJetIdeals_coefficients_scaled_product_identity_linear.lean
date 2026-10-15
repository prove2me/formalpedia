-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coefficients_scaled_product_identity_linear
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:34:51.286233+00:00
-- url     : https://prove2.me/submissions/fe8d8c94-9827-4b50-b344-e3843265159e

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_coefficients_scaled_product_vanish_below_degree
import Theorems.Thm_coefficients_scaled_product_degree_boundary

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (m : Fin n →₀ Nat)
    (c : Complex)
    (D : Nat)
    (e : Fin n → Nat)
    (hdeg : (∑ i, m i) = D) :
    ((∑ i, e i) < D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        ((algebraMap Complex (MvPowerSeries (Fin n) Complex) c) *
          m.prod (fun i k => phi i ^ k)) = 0) ∧
    ((∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        ((algebraMap Complex (MvPowerSeries (Fin n) Complex) c) *
          m.prod (fun i k => phi i ^ k)) =
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.monomial m c)) := by
  have hbelow := coefficients_scaled_product_vanish_below_degree
    phi hzero m D e hdeg
  have hboundary := coefficients_scaled_product_degree_boundary
    phi hzero hlinear m D e hdeg
  constructor
  · intro he
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul]
    rw [hbelow he]
    simp
  · intro he
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul]
    rw [hboundary he]
    simp [MvPolynomial.coeff_monomial, mul_ite]
