-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_force_coordinate_coefficients_of_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T18:54:05.844185+00:00
-- url     : https://prove2.me/submissions/02f0ba64-121e-4d64-9690-4be2140942e1

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_truncation_preserves_filtered_substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ)
    (c : Fin m → ℂ) (T : Fin m → ℕ)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (B : ℝ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet c P) = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < B →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (localCoordinatePolynomial c T P) = 0 := by
  simpa [AdmissibleFormalInterpolation.formalJet, localCoordinatePolynomial,
    InterpolationMatrix.truncatedLog] using
    (OAI.PiExponent.LogarithmicJetIdeals.weighted_truncation_preserves_filtered_substitution
      (q := InterpolationMatrix.rowWeights v0 theta w) (hq := hv)
      (c := c) (G := fun _ => PowerSeries.log ℂ) (T := T) (hT := hT)
      (B := B) (P := P) hcoeff)