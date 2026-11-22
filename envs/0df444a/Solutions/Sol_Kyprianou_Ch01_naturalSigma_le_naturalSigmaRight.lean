-- Prove2me | solution 1 for Kyprianou.Ch01.naturalSigma_le_naturalSigmaRight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:58:31.071943+00:00
-- url     : https://prove2.me/submissions/aea6b874-cd8b-4243-9eb7-9c55d7daebf6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_monotone

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    naturalSigma X t ≤ naturalSigmaRight X t := by
  unfold naturalSigmaRight
  refine le_iInf fun s => le_iInf fun hts => ?_
  exact Kyprianou.Ch01.naturalSigma_monotone X hts.le
