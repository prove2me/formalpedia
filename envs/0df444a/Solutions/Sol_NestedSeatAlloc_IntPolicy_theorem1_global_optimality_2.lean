-- Prove2me | solution 2 for NestedSeatAlloc.IntPolicy.theorem1_global_optimality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T07:05:48.852306+00:00
-- url     : https://prove2.me/submissions/3e59b4bc-30b9-44b4-a9b9-4192002e6a7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_base
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_step_all_seats

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p) :
    IsOptimal P X f p := by
  intro q hq k
  revert q hq
  induction k with
  | zero =>
      intro q hq hk
      omega
  | succ k ih =>
      intro q hq hk s hs
      by_cases hk0 : k = 0
      · subst k
        exact theorem1_global_optimality_base P X f p hM hp q hq s hs
      · have hkpos : 1 ≤ k := by omega
        have h20k :
            InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)) :=
          h20 k hkpos
        have hprev : ∀ t, 0 ≤ t → ∀ q', IsProtectionPolicy q' →
            expRevenue P X f q' k t ≤ expRevenue P X f p k t := by
          intro t ht q' hq'
          exact ih q' hq' hkpos t ht
        exact (theorem1_global_optimality_step_all_seats P X f p k hM hp
          hkpos h20k hprev) s hs q hq
