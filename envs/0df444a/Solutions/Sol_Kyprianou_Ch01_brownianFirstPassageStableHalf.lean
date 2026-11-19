-- Prove2me | solution 1 for Kyprianou.Ch01.brownianFirstPassageStableHalf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:18:15.511149+00:00
-- url     : https://prove2.me/submissions/3a2f2389-3efb-484a-9ae5-0fdc280ef6b9

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
import Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageZeroDiscount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The stable-index-half transform is the zero-drift, unit-variance
    specialisation of the Brownian upper-passage transform, with a separate
    recurrent-Brownian zero-discount boundary. -/
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
  rcases eq_or_lt_of_le hq with hzero | hpositive
  · subst q
    have hbase := Kyprianou.Ch01.brownianFirstPassageZeroDiscount
      P B hB hmeas s hs
    simpa only [mul_zero, Real.sqrt_zero, Real.exp_zero] using hbase
  · have hbase := Kyprianou.Ch01.brownianDiscountedUpperPassage
      P B (1 : ℝ) (0 : ℝ) q s (by norm_num) hpositive hs hB hmeas
    simpa using hbase
