-- Prove2me | solution 3 for Kyprianou.Ch02.smallJumpBandMeasureFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T22:56:56.394329+00:00
-- url     : https://prove2.me/submissions/0b42cc8d-9571-49b7-812e-1e5562c23eec

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (e : ℝ) (he : 0 < e) :
    levyMeasure {x : ℝ | e ≤ |x| ∧ |x| < 1} < ⊤ :=
  lt_of_le_of_lt (measure_mono fun _ hx => hx.1)
    (hlevyMeasure.measure_setOf_abs_ge_lt_top he)
