-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_kronecker
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T23:20:49.51268+00:00
-- url     : https://prove2.me/submissions/03468f8f-30bc-413c-bf8b-db5f93ac51b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficients_surjective

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hindex : Function.Injective (fun a : α => (slot a, degree a)))
    (hcenters : ∀ i j, i ≠ j → ∃ k, center i k ≠ center j k)
    (a : α) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center (slot b)) P) = if b = a then 1 else 0 := by
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_surjective
      center slot degree hindex hcenters (fun b => if b = a then 1 else 0)
  exact ⟨P, fun b => hP b⟩