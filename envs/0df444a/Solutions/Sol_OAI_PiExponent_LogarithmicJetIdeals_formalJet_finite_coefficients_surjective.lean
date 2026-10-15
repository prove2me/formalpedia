-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_finite_coefficients_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:33:03.215708+00:00
-- url     : https://prove2.me/submissions/9c757ec2-61f9-4add-8064-db2eaf2bcf00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomial_finite_coefficient_interpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_truncation_surjective

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : Fin m → ℂ) (degree : α → Fin (m + 1) → ℕ)
    (hdegree : Function.Injective degree) (value : α → ℂ) :
    ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet center Q) = value b := by
  obtain ⟨R, hR⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.polynomial_finite_coefficient_interpolation
      degree hdegree value
  let T : ℕ := Finset.univ.sup (fun b : α => (∑ i : Fin (m + 1), degree b i) + 1)
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_truncation_surjective
      center R T
  refine ⟨Q, fun b => ?_⟩
  have hbound : (∑ i : Fin (m + 1), degree b i) < T := by
    have hb : (∑ i : Fin (m + 1), degree b i) + 1 ≤ T := by
      dsimp [T]
      exact Finset.le_sup
        (s := (Finset.univ : Finset α))
        (f := fun a : α => (∑ i : Fin (m + 1), degree a i) + 1)
        (Finset.mem_univ b)
    omega
  rw [hQ (degree b) hbound]
  exact hR b