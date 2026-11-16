-- Prove2me | solution 1 for Kyprianou.Ch01.naturalSigma_measurable_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:25:04.696207+00:00
-- url     : https://prove2.me/submissions/05cc0644-a495-49db-bd74-ab4f88b29175

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
    (X : ℝ≥0 → Ω → ℝ) (u s : ℝ≥0) (hus : u ≤ s) :
    @Measurable Ω ℝ (naturalSigma X s) inferInstance (X u) := by
  change @Measurable Ω ℝ (PerfCorrMSQ.natFiltr X s)
    inferInstance (X u)
  unfold PerfCorrMSQ.natFiltr
  apply Measurable.of_comap_le
  exact le_iSup_of_le u (le_iSup_of_le hus le_rfl)
