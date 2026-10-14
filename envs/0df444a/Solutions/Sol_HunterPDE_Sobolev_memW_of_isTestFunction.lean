-- Prove2me | solution 1 for HunterPDE.Sobolev.memW_of_isTestFunction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:07:42.989286+00:00
-- url     : https://prove2.me/submissions/074593c0-e256-4795-a6a7-3f41ce61d63a

import Theorems.Thm_HunterPDE_Sobolev_hasWeakDeriv_of_contDiff
import Theorems.Thm_HunterPDE_Sobolev_IsTestFunction_iteratedPartial
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open MeasureTheory HunterPDE.Sobolev
set_option autoImplicit false

theorem solution {n k : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : IsTestFunction Set.univ φ) : MemW k p Set.univ φ := by
  refine ⟨hφ.1.continuous.continuousOn.locallyIntegrableOn MeasurableSet.univ, ?_⟩
  intro α hα
  refine ⟨iteratedPartial α φ, hasWeakDeriv_of_contDiff φ hφ.1 α, ?_⟩
  have hd := IsTestFunction.iteratedPartial hφ α
  simpa only [Measure.restrict_univ] using hd.1.continuous.memLp_of_hasCompactSupport hd.2.1
