-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficient_functionals_independent
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:06:38.940706+00:00
-- url     : https://prove2.me/submissions/807c2454-32ad-4ea3-a7dc-1f68b4d33978

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficients_interpolating_polynomials
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_linearIndependent_of_kronecker_pairing
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    ∃ L : ι → MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ] ℂ,
      LinearIndependent ℂ L ∧
      ∀ x P, L x P =
        MvPowerSeries.coeff (exponent x) (formalJet (c x) P) := by
  classical
  let L : ι → MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ] ℂ := fun x =>
    (MvPowerSeries.coeff (exponent x)).comp (formalJet (c x)).toLinearMap
  obtain ⟨Q, hQ⟩ := formalJet_coefficients_interpolating_polynomials c exponent hindex
  refine ⟨L, ?_, ?_⟩
  · exact linearIndependent_of_kronecker_pairing L Q hQ
  · intro x P
    rfl