-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_finiteColength
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:56:38.676339+00:00
-- url     : https://prove2.me/submissions/29169e25-98c3-4d25-b813-e972fcc6afb8

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_finiteDimensional
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeals_pairwiseComaximal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finiteDimensional_of_pairwiseComaximalProduct

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (hdist : ∀ j₁ j₂ : Fin K, j₁ ≠ j₂ → c j₁ ≠ c j₂) :
    FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ logarithmicCentersIdeal c T e) := by
  classical
  delta logarithmicCentersIdeal
  exact
    (OAI.PiExponent.FormalInterpolation.finiteDimensional_of_pairwiseComaximalProduct
      (fun j : Fin K => logarithmicCenterIdeal (c j) T e)
      (fun j =>
        OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_finiteDimensional
          (c j) T e he)
      (fun j₁ j₂ hne =>
        OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwiseComaximal
          (c j₁) (c j₂) T e he (hdist j₁ j₂ hne)))