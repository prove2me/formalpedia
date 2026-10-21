-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_interpolating_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:28:42.44744+00:00
-- url     : https://prove2.me/submissions/ae93f882-d5ab-4293-a747-602a2e6f436a

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finite_linear_functionals_interpolation
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalJet_coefficient_functionals_linearIndependent

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    ∃ Q : ι → MvPolynomial (Fin (m + 1)) ℂ,
      ∀ x y, MvPowerSeries.coeff (exponent x) (formalJet (c x) (Q y)) =
        if x = y then 1 else 0 := by
  let f : ι → MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ] ℂ :=
    fun x => (MvPowerSeries.coeff (exponent x)).comp
      (formalJet (c x)).toLinearMap
  have hf : LinearIndependent ℂ f := by
    simpa [f] using
      OAI.PiExponent.AdmissibleFormalInterpolation.formalJet_coefficient_functionals_linearIndependent
        c exponent hindex
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.AdmissibleFormalInterpolation.finite_linear_functionals_interpolation f hf
  refine ⟨Q, ?_⟩
  intro x y
  simpa [f] using hQ x y