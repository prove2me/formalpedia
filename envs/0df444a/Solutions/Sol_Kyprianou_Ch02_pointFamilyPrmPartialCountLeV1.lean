-- Prove2me | solution 1 for Kyprianou.Ch02.pointFamilyPrmPartialCountLeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:08:18.694062+00:00
-- url     : https://prove2.me/submissions/6b471513-0620-4140-ae23-14a559544f94

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (A : Set E) (hA : MeasurableSet A) (n : ℕ) (ω : Ω) :
    (ProbabilityTheory.prmPartialCount K Y A n ω : ENNReal) ≤
      ProbabilityTheory.poissonRandomMeasure K Y ω A := by
  classical
  rw [ProbabilityTheory.poissonRandomMeasure_apply hA,
    ProbabilityTheory.prmPartialCount, Nat.cast_sum]
  exact ENNReal.sum_le_tsum (Finset.range (n + 1))
