-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41MeasurableGridInfimumV26
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:43:56.009434+00:00
-- url     : https://prove2.me/submissions/c321f722-f7e2-40db-b248-1c9ba2c968e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (q : ℕ → NNReal) (h : NNReal) :
    Measurable (fun f : NNReal → ℝ => ⨅ k : ℕ, f (min (q k) h)) := by
  exact Measurable.iInf (fun k => measurable_pi_apply (min (q k) h))
