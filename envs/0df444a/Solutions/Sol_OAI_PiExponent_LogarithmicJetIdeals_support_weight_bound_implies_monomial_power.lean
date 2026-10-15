-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.support_weight_bound_implies_monomial_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T19:51:04.174998+00:00
-- url     : https://prove2.me/submissions/80a1aa5a-c7a7-48c6-85ab-fb9b1cf181d1

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_monomial_power_of_weight_bound
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_support_monomials_mem_ideal

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hsupport : ∀ d ∈ Q.support,
      (((n + m : ℕ) : ℝ) * R) ≤ ∑ i, ρ i * (d i : ℝ)) :
    Q ∈ (Ideal.span (Set.range (fun i : Fin (m + 1) =>
      MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n := by
  let J : Ideal (MvPolynomial (Fin (m + 1)) ℂ) :=
    Ideal.span (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i ^ e i))
  have hmono : ∀ d ∈ Q.support, MvPolynomial.monomial d (1 : ℂ) ∈ J ^ n := by
    intro d hd
    exact OAI.PiExponent.LogarithmicJetIdeals.monomial_power_of_weight_bound
      e ρ R hR hρ he hscale n d (hsupport d hd)
  exact OAI.PiExponent.LogarithmicJetIdeals.support_monomials_mem_ideal
    (J ^ n) Q hmono