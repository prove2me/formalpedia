-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coordinate_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T22:25:42.071466+00:00
-- url     : https://prove2.me/submissions/82b01420-888b-4a69-835c-8781492869b2

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

private theorem liftLogSeries_coe_polynomial {m : ℕ} (p : Polynomial ℂ) :
    liftLogSeries m (p : PowerSeries ℂ) =
      Polynomial.eval₂ MvPowerSeries.C (MvPowerSeries.X (0 : Fin (m + 1))) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [Polynomial.coe_add, hp, hq]
  | monomial n a =>
      have hC : (MvPowerSeries.finSuccEquiv ℂ m).symm
          (PowerSeries.C (MvPowerSeries.C a)) = MvPowerSeries.C a := by
        apply (MvPowerSeries.finSuccEquiv ℂ m).injective
        simp
      have hX : (MvPowerSeries.finSuccEquiv ℂ m).symm PowerSeries.X =
          MvPowerSeries.X (0 : Fin (m + 1)) := by
        apply (MvPowerSeries.finSuccEquiv ℂ m).injective
        simp
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [liftLogSeries, hC, hX]

private theorem aeval_polynomial_in_zero {m : ℕ}
    (f : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (p : Polynomial ℂ) :
    MvPolynomial.aeval f
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin (m + 1))) p) =
      Polynomial.eval₂ MvPowerSeries.C (f 0) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq]
  | monomial n a =>
      simp [MvPowerSeries.algebraMap_apply]

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (G : Fin m → PowerSeries ℂ)
    (H : Fin m → Polynomial ℂ) (i : Fin (m + 1)) :
    MvPolynomial.aeval
      (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
        (fun j => MvPowerSeries.X j.succ +
          liftLogSeries m (G j - (H j : PowerSeries ℂ))) :
        Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
      ((Fin.cases (1 + MvPolynomial.X (0 : Fin (m + 1)))
        (fun j => MvPolynomial.C (c j) + MvPolynomial.X j.succ +
          Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (H j)) :
        Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ) i) =
    Fin.cases (1 + MvPowerSeries.X (0 : Fin (m + 1)))
      (fun j => MvPowerSeries.C (c j) + MvPowerSeries.X j.succ +
        liftLogSeries m (G j)) i := by
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
      simp [aeval_polynomial_in_zero, liftLogSeries_coe_polynomial,
        MvPowerSeries.algebraMap_apply, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]