-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_surjective_of_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T23:24:53.412905+00:00
-- url     : https://prove2.me/submissions/90d671df-b8f1-4feb-a694-48b2700a7fb9

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hdiag : ∀ a : α,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
        ∀ b : α,
          MvPowerSeries.coeff
            (Finsupp.equivFunOnFinite.symm (degree b))
            (formalJet (center (slot b)) P) = if b = a then 1 else 0) :
    Function.Surjective (fun P : MvPolynomial (Fin (m + 1)) ℂ =>
      fun a : α => MvPowerSeries.coeff
        (Finsupp.equivFunOnFinite.symm (degree a))
        (formalJet (center (slot a)) P)) := by
  classical
  choose W hW using hdiag
  intro y
  refine ⟨∑ a : α, MvPolynomial.C (y a) * W a, ?_⟩
  funext b
  simp only [map_sum, map_mul]
  simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul, hW]
