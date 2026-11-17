-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassageNaturalRightStoppingContinuousV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:58:55.374687+00:00
-- url     : https://prove2.me/submissions/67c87ac8-091b-4259-87c8-2ad7666b196a

import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_rawNaturalPast_later
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (hs : 0 < s) :
    Kyprianou.Ch01.IsNaturalRightStoppingTime X
      (Kyprianou.Ch01.firstUpperPassage X s) := by
  intro t
  change @MeasurableSet Ω
    (⨅ v : ℝ≥0, ⨅ (_hv : t < v), Kyprianou.Ch01.naturalSigma X v)
    {ω | Kyprianou.Ch01.firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0)}
  rw [MeasurableSpace.measurableSet_iInf]
  intro v
  rw [MeasurableSpace.measurableSet_iInf]
  intro htv
  exact Kyprianou.Ch01.firstUpperPassage_le_rawNaturalPast_later
    X hContinuous s t v htv
