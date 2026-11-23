-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPoissonLocallyFiniteStepRepresentationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:01:31.409821+00:00
-- url     : https://prove2.me/submissions/8a41aa81-405b-4b6e-a108-ee184746a67c

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteWindowDiracLawV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteWindowStepFromDiracV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hSupport : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ (s : Finset (ℝ × ℝ))
      (weight : ℝ × ℝ → ℝ), ∀ t : ℝ≥0, t ≤ (T : ℝ≥0) →
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) =
        ∑ p ∈ s, if p.1 ≤ (t : ℝ) then weight p else 0 := by
  have hDirac :=
    Kyprianou.Ch02.prmFiniteWindowDiracLawV1 P ν N B hB hfinite
  exact Kyprianou.Ch02.prmFiniteWindowStepFromDiracV1
    P ν N B hB hfinite hDirac
