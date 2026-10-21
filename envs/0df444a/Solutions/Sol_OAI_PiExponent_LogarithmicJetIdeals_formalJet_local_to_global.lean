-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_local_to_global
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:14:56.926873+00:00
-- url     : https://prove2.me/submissions/83c78b27-7d77-4f7c-a66e-4ec3f68ee15c

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_jet_gluing

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hcenters : ∀ i j, i ≠ j → ∃ k, center i k ≠ center j k)
    (value : α → ℂ)
    (hlocal : ∀ i : ι, ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α, slot b = i →
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center i) Q) = value b) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center (slot b)) P) = value b := by
  let Q : ι → MvPolynomial (Fin (m + 1)) ℂ := fun i => Classical.choose (hlocal i)
  have hQ (i : ι) : ∀ b : α, slot b = i →
      MvPowerSeries.coeff
        (Finsupp.equivFunOnFinite.symm (degree b))
        (formalJet (center i) (Q i)) = value b :=
    Classical.choose_spec (hlocal i)
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_jet_gluing
      center slot degree hcenters Q
  refine ⟨P, fun b => ?_⟩
  rw [hP b]
  exact hQ (slot b) b rfl