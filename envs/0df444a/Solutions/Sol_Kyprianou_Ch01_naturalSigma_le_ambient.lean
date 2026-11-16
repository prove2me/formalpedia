-- Prove2me | solution 1 for Kyprianou.Ch01.naturalSigma_le_ambient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:34:36.969098+00:00
-- url     : https://prove2.me/submissions/d3979134-d444-48c2-a8cd-a5ab3685f9a6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (s : ℝ≥0) :
    naturalSigma X s ≤ (inferInstance : MeasurableSpace Ω) := by
  change PerfCorrMSQ.natFiltr X s ≤ (inferInstance : MeasurableSpace Ω)
  unfold PerfCorrMSQ.natFiltr
  refine iSup_le fun u => iSup_le fun hu => ?_
  exact (hmeas u).comap_le
