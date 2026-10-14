-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formal_jet_interpolation_of_injective_requests
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T00:25:08.948883+00:00
-- url     : https://prove2.me/submissions/079a1fda-3da5-4ea5-bdfe-5378738d1357
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_family_linear_functional_interpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficient_functionals_linearIndependent

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} {ι : Type} [Fintype ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (values : ι → ℂ)
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ x, MvPowerSeries.coeff (exponent x)
        (formalJet (c x) P) = values x := by
  let L : ι → MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ] ℂ := fun x =>
    { toFun := fun P => MvPowerSeries.coeff (exponent x) (formalJet (c x) P)
      map_add' := by simp [formalJet]
      map_smul' := by simp [formalJet] }
  have hL : LinearIndependent ℂ L :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficient_functionals_linearIndependent
      c exponent hindex
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_family_linear_functional_interpolation
      L hL values
  exact ⟨P, hP⟩