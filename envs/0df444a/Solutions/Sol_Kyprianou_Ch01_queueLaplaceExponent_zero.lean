-- Prove2me | solution 1 for Kyprianou.Ch01.queueLaplaceExponent_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:28:22.083693+00:00
-- url     : https://prove2.me/submissions/4aabf837-b7c8-4d84-9c8d-48217bbe8216

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (F : Measure ℝ) :
    queueLaplaceExponent rate F 0 = 0 := by
  simp [queueLaplaceExponent]
