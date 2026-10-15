-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_force_coordinate_coefficients
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T17:46:18.287985+00:00
-- url     : https://prove2.me/submissions/9b074547-7db6-4fc6-a82d-82378651a87e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_low_weight_formal_coefficients_force_coordinate_coefficients_of_tail_bound

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
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        (((n + m : ℕ) : ℝ) * R) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (localCoordinatePolynomial c T P) = 0 := by
  exact OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_force_coordinate_coefficients_of_tail_bound
    v0 theta w c T hv hT (((n + m : ℕ) : ℝ) * R) P hcoeff
