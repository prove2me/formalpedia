-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteWindowDiracLawV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:43:06.044381+00:00
-- url     : https://prove2.me/submissions/25610408-5fd9-408a-8863-fc1c96489f2b

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMIntegerValuedAllNaturalWindowsV2
import Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteDiracV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      (N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) =
        ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) {p} • Measure.dirac p := by
  filter_upwards
    [Kyprianou.Ch02.finiteRegionPRMIntegerValuedAllNaturalWindowsV2
      P ν N B hB hfinite] with ω hω
  intro T
  exact Kyprianou.Ch02.integerValuedFiniteDiracV1
    ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B))
    (hω T)
