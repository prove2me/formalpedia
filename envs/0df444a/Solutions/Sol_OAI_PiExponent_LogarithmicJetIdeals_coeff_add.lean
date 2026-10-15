-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_add
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:35:02.629904+00:00
-- url     : https://prove2.me/submissions/6f6eb813-a648-4040-b3e9-45314ed19d70

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (Q R : MvPolynomial (Fin n) Complex)
    (e : Fin n → Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi (Q + R)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi Q) +
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi R) := by
  simp