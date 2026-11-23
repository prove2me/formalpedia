-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteWindowDiracLawV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:20:00.781057+00:00
-- url     : https://prove2.me/submissions/14703a61-32ae-4642-b21a-2fa3e35e7bd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMIntegerValuedAllNaturalWindowsV1
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
    [Kyprianou.Ch02.finiteRegionPRMIntegerValuedAllNaturalWindowsV1
      P ν N B hB hfinite] with ω hω
  intro T
  exact Kyprianou.Ch02.integerValuedFiniteDiracV1
    ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B))
    (hω T)
