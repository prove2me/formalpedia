-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coordinate_coefficients_imply_local_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T17:19:06.633872+00:00
-- url     : https://prove2.me/submissions/b1402698-992a-47e9-9fe8-58f56b0b9ba6

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coordinate_coefficients_imply_monomial_power
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coordinate_monomial_power_implies_local_power

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoord : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, ρ i * (a i : ℝ)) < (((n + m : ℕ) : ℝ) * R) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (localCoordinatePolynomial c T P) = 0) :
    P ∈ (localJetIdeal c T e) ^ n := by
  have hmon : localCoordinatePolynomial c T P ∈
      (Ideal.span (Set.range (fun i : Fin (m + 1) =>
        MvPolynomial.X i ^ e i)) :
          Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n := by
    exact OAI.PiExponent.LogarithmicJetIdeals.coordinate_coefficients_imply_monomial_power
      e ρ R hR hρ he hscale n (localCoordinatePolynomial c T P) hcoord
  exact OAI.PiExponent.LogarithmicJetIdeals.coordinate_monomial_power_implies_local_power
    c T e n P hmon