-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem2_tail_derivative_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:38:57.228975+00:00
-- url     : https://prove2.me/submissions/987e95bb-804d-43b3-9c11-88bbaeb07676

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hderiv : ∀ s, 0 ≤ s →
      HasDerivWithinAt (expRevenue P X f p 1)
        (f 1 * P.real {ω | s < X 1 ω}) (Set.Ici s) s)
    (htail : ∃ s, 0 < s ∧ f 1 * P.real {ω | s < X 1 ω} < f 2) :
    ∃ s, 0 < s ∧ ∃ r,
      HasDerivWithinAt (expRevenue P X f p 1) r (Set.Ici s) s ∧ r < f 2 := by
  obtain ⟨s, hs, hlt⟩ := htail
  refine ⟨s, hs, f 1 * P.real {ω | s < X 1 ω}, ?_, hlt⟩
  exact hderiv s (le_of_lt hs)
