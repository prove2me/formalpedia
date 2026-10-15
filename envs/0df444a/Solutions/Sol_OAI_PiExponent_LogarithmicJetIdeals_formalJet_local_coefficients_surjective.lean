-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_local_coefficients_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:23:44.558685+00:00
-- url     : https://prove2.me/submissions/8f59c59a-6706-48cb-95cf-8def52e0b05f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_finite_coefficients_surjective
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hindex : Function.Injective (fun a : α => (slot a, degree a)))
    (value : α → ℂ) :
    ∀ i : ι, ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α, slot b = i →
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center i) Q) = value b := by
  classical
  intro i
  let β := {a : α // slot a = i}
  have hdegree : Function.Injective (fun b : β => degree b.1) := by
    intro a b hab
    apply Subtype.ext
    apply hindex
    apply Prod.ext
    · exact a.2.trans b.2.symm
    · exact hab
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_finite_coefficients_surjective
      (α := β) (center := center i) (degree := fun b => degree b.1)
      hdegree (fun b => value b.1)
  refine ⟨Q, ?_⟩
  intro b hb
  exact hQ ⟨b, hb⟩