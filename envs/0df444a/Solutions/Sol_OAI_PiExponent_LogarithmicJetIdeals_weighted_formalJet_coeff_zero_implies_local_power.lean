-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_local_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T21:18:59.313029+00:00
-- url     : https://prove2.me/submissions/1b1d5b4f-7e35-4fd8-b229-28fb3a589652
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_formalJet_coeff_zero_implies_local_power_coeff_transfer
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_coordinate_coefficients_imply_power
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_coordinates_preserve_ideal_power

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (S : ℝ)
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hS : 0 < S)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i ≤ S)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ (a : Fin (m + 1) → ℕ),
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        ((n + m : ℕ) : ℝ) * S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet c P) = 0) :
    P ∈ localJetIdeal c T e ^ n := by
  let Q := localCoordinatePolynomial c T P
  have hQcoeff :
      ∀ a : Fin (m + 1) → ℕ,
        (∑ i, a i / e i : ℕ) < n →
        MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q = 0 := by
    exact OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_local_power_coeff_transfer
      v0 theta w S c T e hS hv he hscale hT n P hcoeff
  have hQ :
      Q ∈ Ideal.span (Set.range (fun i : Fin (m + 1) =>
        (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i)) ^ n := by
    exact OAI.PiExponent.LogarithmicJetIdeals.local_coordinate_coefficients_imply_power
      (m := m) (e := e) he n Q hQcoeff
  exact OAI.PiExponent.LogarithmicJetIdeals.local_coordinates_preserve_ideal_power
    (m := m) c T e n P hQ