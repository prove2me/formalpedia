-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_imply_local_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T13:51:52.14679+00:00
-- url     : https://prove2.me/submissions/5cbfc681-22a6-4fff-a04d-338cb508a9e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_low_weight_formal_coefficients_force_coordinate_coefficients
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coordinate_coefficients_imply_local_power

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (R : ℝ)
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hR : 0 < R)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        (((n + m : ℕ) : ℝ) * R) →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet c P) = 0) :
    P ∈ (localJetIdeal c T e) ^ n := by
  have hcoord :=
    OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_force_coordinate_coefficients
      v0 theta w R c T e hR hv he hscale hT n P hcoeff
  exact
    OAI.PiExponent.LogarithmicJetIdeals.coordinate_coefficients_imply_local_power
      c T e (InterpolationMatrix.rowWeights v0 theta w) R hR hv he hscale n P hcoord