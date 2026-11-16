-- Prove2me | solution 1 for Kyprianou.Ch01.naturalSigma_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T22:03:14.954638+00:00
-- url     : https://prove2.me/submissions/53afbc1e-2a1f-4233-a46b-3382731e5169

import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

/-- Past observation sigma-fields are nested with increasing time. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    Kyprianou.Ch01.naturalSigma X s ≤ Kyprianou.Ch01.naturalSigma X t := by
  change PerfCorrMSQ.natFiltr X s ≤ PerfCorrMSQ.natFiltr X t
  unfold PerfCorrMSQ.natFiltr
  refine iSup_le fun u => iSup_le fun hu => ?_
  exact le_iSup_of_le u (le_iSup_of_le (hu.trans hst) le_rfl)
