-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.exists_formalJet_coefficient_dualFamily
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T08:49:49.000977+00:00
-- url     : https://prove2.me/submissions/d53b9128-fcba-49d0-8e17-5fd39243fcf1

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficient_functionals_independent
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_linearIndependent_functionals_dualFamily

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    ∃ Q : ι → MvPolynomial (Fin (m + 1)) ℂ,
      ∀ x y,
        MvPowerSeries.coeff (exponent x) (formalJet (c x) (Q y)) =
          if x = y then 1 else 0 := by
  obtain ⟨L, hL, hcoeff⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficient_functionals_independent
      c exponent hindex
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.linearIndependent_functionals_dualFamily L hL
  refine ⟨Q, ?_⟩
  intro x y
  rw [← hcoeff x (Q y)]
  exact hQ x y