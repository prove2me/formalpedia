-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.monomial_power_of_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T20:39:58.107925+00:00
-- url     : https://prove2.me/submissions/f98d86b7-af42-47f1-b53d-58c63615e017

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weight_bound_implies_quotient_sum
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_quotient_capacity_allocation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_monomial_mem_power_of_coordinate_allocation

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (d : Fin (m + 1) →₀ ℕ)
    (hweight : (((n + m : ℕ) : ℝ) * R) ≤ ∑ i, ρ i * (d i : ℝ)) :
    MvPolynomial.monomial d (1 : ℂ) ∈
      (Ideal.span (Set.range (fun i : Fin (m + 1) =>
        MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n := by
  have hquot := weight_bound_implies_quotient_sum e ρ R hR hρ he hscale n d hweight
  obtain ⟨k, hk, hdiv⟩ := quotient_capacity_allocation e d n hquot
  exact monomial_mem_power_of_coordinate_allocation e n d k hk hdiv
