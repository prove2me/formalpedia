-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_conditional_concavity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:53:37.388712+00:00
-- url     : https://prove2.me/submissions/c8d6ee74-a57a-40ee-97bc-5621b3ee1058
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_conditional_concavity_base
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_conditional_concavity_step
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_conditional_concavity_assembly

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (h20 : SubdiffCondition P X f p) :
    ∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y) := by
  apply theorem1_conditional_concavity_assembly P X f p hM hp h20
  · have hbase := theorem1_conditional_concavity_base P X f p hM hp
    exact hbase
  · intro k y hk hy h20k hprev
    have hstep := theorem1_conditional_concavity_step P X f p k y hM hp hk hy h20k hprev
    exact hstep
