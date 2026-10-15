-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_formalJet_coefficients_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T23:05:19.339752+00:00
-- url     : https://prove2.me/submissions/6c30e599-d05f-4794-a671-b6c513072a86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficients_kronecker
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficients_surjective_of_kronecker

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {ι α : Type} [Fintype α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hindex : Function.Injective (fun a : α => (slot a, degree a)))
    (hcenters : ∀ i j, i ≠ j → ∃ k, center i k ≠ center j k) :
    Function.Surjective (fun P : MvPolynomial (Fin (m + 1)) ℂ =>
      fun a : α => MvPowerSeries.coeff
        (Finsupp.equivFunOnFinite.symm (degree a))
        (formalJet (center (slot a)) P)) := by
  classical
  apply OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_surjective_of_kronecker
    center slot degree
  intro a
  exact OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_kronecker
    center slot degree hindex hcenters a