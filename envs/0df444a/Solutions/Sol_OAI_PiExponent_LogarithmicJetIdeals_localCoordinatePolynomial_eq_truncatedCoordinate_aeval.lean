-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.localCoordinatePolynomial_eq_truncatedCoordinate_aeval
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:58:27.795977+00:00
-- url     : https://prove2.me/submissions/14a7b37e-315d-4b69-af25-5896baa138eb

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

/-!
# Polynomial and power-series coordinates for the logarithmic jet

`localCoordinatePolynomial` substitutes polynomials in the local jet coordinates. This file
identifies its image in the multivariable power-series ring with the evaluation of the same
polynomial in the corresponding power-series coordinates, using the lifted formal logarithm
`liftLogSeries`.
-/

namespace P2MLocalCoordinatePort

variable {m : ℕ}

/-- The lifted formal logarithm sends the constant power series to the constant power series. -/
theorem p2m_liftLogSeries_C (a : ℂ) :
    liftLogSeries m (PowerSeries.C a) = MvPowerSeries.C a := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  simp [liftLogSeries]

/-- The lifted formal logarithm sends the identity power series to the coordinate `X 0`. -/
theorem p2m_liftLogSeries_X :
    liftLogSeries m (PowerSeries.X : PowerSeries ℂ) = MvPowerSeries.X (0 : Fin (m + 1)) := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  simp [liftLogSeries]

/-- Coercing to power series the polynomial obtained by placing a one-variable polynomial in the
coordinate `X 0` gives the lifted formal logarithm of that polynomial. -/
theorem p2m_eval₂_coe_eq_liftLogSeries (F : Polynomial ℂ) :
    ((Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin (m + 1))) F :
        MvPolynomial (Fin (m + 1)) ℂ) : MvPowerSeries (Fin (m + 1)) ℂ) =
      liftLogSeries m (F : PowerSeries ℂ) := by
  let f : Polynomial ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
    MvPolynomial.coeToMvPowerSeries.ringHom.comp
      (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin (m + 1))))
  let g : Polynomial ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
    (liftLogSeries m).comp Polynomial.coeToPowerSeries.ringHom
  have hfg : f = g := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [f, g, RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
        MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.eval₂_C, MvPolynomial.coe_C, Polynomial.coe_C]
      exact (p2m_liftLogSeries_C (m := m) a).symm
    · simp only [f, g, RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
        MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.eval₂_X, MvPolynomial.coe_X, Polynomial.coe_X]
      exact (p2m_liftLogSeries_X (m := m)).symm
  have := congrArg (fun φ : Polynomial ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ => φ F) hfg
  simpa [f, g] using this

end P2MLocalCoordinatePort

theorem solution {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    (localCoordinatePolynomial c T P : MvPowerSeries (Fin (m + 1)) ℂ) =
      MvPolynomial.aeval
        (Fin.cases (1 + MvPowerSeries.X 0)
          (fun i : Fin m => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
            liftLogSeries m (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ))) P := by
  have hdef : localCoordinatePolynomial c T P =
      MvPolynomial.aeval
        (Fin.cases (1 + MvPolynomial.X 0)
          (fun i : Fin m => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
            Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
              (InterpolationMatrix.truncatedLog (T i)))) P := rfl
  rw [hdef]
  clear hdef
  -- Pointwise comparison of the two coordinate systems.
  have hcoord : ∀ n : Fin (m + 1),
      ((Fin.cases (1 + MvPolynomial.X 0)
        (fun i : Fin m => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
          Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
            (InterpolationMatrix.truncatedLog (T i))) n : MvPolynomial (Fin (m + 1)) ℂ) :
        MvPowerSeries (Fin (m + 1)) ℂ) =
      Fin.cases (1 + MvPowerSeries.X 0)
        (fun i : Fin m => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
          liftLogSeries m (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ)) n := by
    intro n
    induction n using Fin.cases with
    | zero => simp
    | succ i =>
      simp only [Fin.cases_succ, MvPolynomial.coe_add, MvPolynomial.coe_C,
        MvPolynomial.coe_X, P2MLocalCoordinatePort.p2m_eval₂_coe_eq_liftLogSeries]
  -- Induction on the polynomial.
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPowerSeries.c_eq_algebraMap]
  | add p q hp hq => simp only [map_add, MvPolynomial.coe_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.coe_mul]
    rw [hp, hcoord n]
