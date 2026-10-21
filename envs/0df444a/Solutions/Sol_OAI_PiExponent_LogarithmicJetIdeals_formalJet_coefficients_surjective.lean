-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:01:11.201167+00:00
-- url     : https://prove2.me/submissions/cefe6804-6180-41c3-9ade-a4c668bd832f

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_local_coefficients_surjective
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_local_to_global

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hindex : Function.Injective (fun a : α => (slot a, degree a)))
    (hcenters : ∀ i j, i ≠ j → ∃ k, center i k ≠ center j k)
    (value : α → ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center (slot b)) P) = value b := by
  exact OAI.PiExponent.LogarithmicJetIdeals.formalJet_local_to_global
    center slot degree hcenters value
    (OAI.PiExponent.LogarithmicJetIdeals.formalJet_local_coefficients_surjective
      center slot degree hindex value)