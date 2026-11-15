-- Prove2me | solution 1 for Kyprianou.Ch01.naturalSigma_eq_natFiltr
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:13:49.65097+00:00
-- url     : https://prove2.me/submissions/d525a402-f99d-4afe-8492-063d30f29fee

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    Kyprianou.Ch01.naturalSigma X t = PerfCorrMSQ.natFiltr X t := by
  rfl
