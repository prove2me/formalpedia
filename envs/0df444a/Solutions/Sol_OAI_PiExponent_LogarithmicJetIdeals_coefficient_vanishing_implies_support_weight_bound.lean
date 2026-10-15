-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coefficient_vanishing_implies_support_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T18:59:47.689622+00:00
-- url     : https://prove2.me/submissions/dae595f8-1871-4073-836b-297d73a2e7c8

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

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
    ∀ d ∈ Q.support,
      (((n + m : ℕ) : ℝ) * R) ≤ ∑ i, ρ i * (d i : ℝ) := by
  intro d hd
  by_contra hbound
  have hlt : (∑ i, ρ i * (d i : ℝ)) < (((n + m : ℕ) : ℝ) * R) :=
    lt_of_not_ge hbound
  have hzero := hcoord (fun i => d i) (by simpa using hlt)
  have hexp : InterpolationMatrix.exponentVector (fun i => d i) = d := by
    ext i
    simp [InterpolationMatrix.exponentVector]
  have hcoeff : MvPolynomial.coeff d Q ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  apply hcoeff
  rw [← hexp]
  exact hzero