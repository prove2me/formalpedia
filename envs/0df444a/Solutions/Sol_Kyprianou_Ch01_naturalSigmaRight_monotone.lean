-- Prove2me | solution 1 for Kyprianou.Ch01.naturalSigmaRight_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:49:40.164244+00:00
-- url     : https://prove2.me/submissions/e1bf68f6-bd7e-4099-843f-0050fe6bb336

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    naturalSigmaRight X s ≤ naturalSigmaRight X t := by
  unfold naturalSigmaRight
  refine le_iInf fun u => le_iInf fun htu => ?_
  exact (iInf_le _ u).trans
    (iInf_le _ (lt_of_le_of_lt hst htu))
