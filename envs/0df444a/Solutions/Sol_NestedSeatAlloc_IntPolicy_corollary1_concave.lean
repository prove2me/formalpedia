-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.corollary1_concave
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T12:58:21.855766+00:00
-- url     : https://prove2.me/submissions/be907c0c-202d-49d6-9109-f25b634cb6f6

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_corollary1_conditional_revenue_concave
import Theorems.Thm_NestedSeatAlloc_IntPolicy_corollary1_integrate_conditional_concavity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (k : ℕ) (hk : 1 ≤ k)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k))
    (h14 : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1))) :
    ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p (k + 1)) := by
  apply corollary1_integrate_conditional_concavity P X f p hM hp k
  intro y hy
  exact corollary1_conditional_revenue_concave
    P X f p hM hp k hk hconc h14 y hy
