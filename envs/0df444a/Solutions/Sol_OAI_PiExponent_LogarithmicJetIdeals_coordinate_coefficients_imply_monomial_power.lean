-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coordinate_coefficients_imply_monomial_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T18:14:55.706321+00:00
-- url     : https://prove2.me/submissions/3418c163-f03d-4c0a-9164-efaa788805a6

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coefficient_vanishing_implies_support_weight_bound
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_support_weight_bound_implies_monomial_power

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoord : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, ρ i * (a i : ℝ)) < (((n + m : ℕ) : ℝ) * R) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q = 0) :
    Q ∈ (Ideal.span (Set.range (fun i : Fin (m + 1) =>
      MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n := by
  apply OAI.PiExponent.LogarithmicJetIdeals.support_weight_bound_implies_monomial_power
    e ρ R hR hρ he hscale n Q
  exact OAI.PiExponent.LogarithmicJetIdeals.coefficient_vanishing_implies_support_weight_bound
    e ρ R hR hρ he hscale n Q hcoord