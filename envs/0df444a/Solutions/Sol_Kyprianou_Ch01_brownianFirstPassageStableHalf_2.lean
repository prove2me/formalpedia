-- Prove2me | solution 2 for Kyprianou.Ch01.brownianFirstPassageStableHalf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:32:47.932217+00:00
-- url     : https://prove2.me/submissions/0e2747ca-1745-4d19-b7cf-ca6369eb05cd

import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
import Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageZeroDiscount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exercise 1.7 follows from positive Brownian discount and its q=0 boundary. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsLinearBrownian P B 1 0)
    (hmeas : ∀ t : ℝ≥0, Measurable (B t)) :
    ∀ (s q : ℝ), 0 < s → 0 ≤ q →
      Integrable (passageLaplace (firstUpperPassage B s) q) P ∧
      (∫ ω, passageLaplace (firstUpperPassage B s) q ω ∂P) =
        Real.exp (-s * Real.sqrt (2 * q)) := by
  intro s q hs hq
  rcases eq_or_lt_of_le hq with hzero | hpos
  · subst q
    have h := Kyprianou.Ch01.brownianFirstPassageZeroDiscount
      P B hB hmeas s hs
    simpa using h
  · have h := Kyprianou.Ch01.brownianDiscountedUpperPassage
      P B 1 0 q s (by norm_num) hpos hs hB hmeas
    simpa [pow_two] using h
