-- Prove2me | solution 1 for Kyprianou.Ch01.queueWorkload_mono_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:32:53.073178+00:00
-- url     : https://prove2.me/submissions/4761f2c9-e8c9-4514-8437-423399813b3a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (w1 w2 : ℝ) (h : w1 ≤ w2) :
    queueWorkload arrival claims w1 t ω ≤
      queueWorkload arrival claims w2 t ω := by
  unfold queueWorkload
  gcongr
