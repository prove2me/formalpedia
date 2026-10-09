-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.condRevenue_one_frozen_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:02:41.977393+00:00
-- url     : https://prove2.me/submissions/a0e2c483-13ba-46ea-af2a-a58a382a067b

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) (hP : IsProbabilityMeasure P) (y s : ℝ) :
    condRevenue P X f p 1 y s =
      if s < y then f 1 * s else f 1 * y := by
  letI : IsProbabilityMeasure P := hP
  simp [condRevenue, revenue]
