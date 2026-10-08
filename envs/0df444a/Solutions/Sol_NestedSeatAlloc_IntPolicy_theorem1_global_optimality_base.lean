-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_global_optimality_base
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:20:15.059512+00:00
-- url     : https://prove2.me/submissions/6c21d5fd-c9c2-488f-a473-b7834e03c54b

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) :
    ∀ q, IsProtectionPolicy q → ∀ s, 0 ≤ s →
      expRevenue P X f q 1 s ≤ expRevenue P X f p 1 s := by
  intro q hq s hs
  simp [expRevenue, revenue]
