-- Prove2me | solution 2 for NestedSeatAlloc.IntPolicy.theorem1_subdiff_condition_optimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:57:03.480075+00:00
-- url     : https://prove2.me/submissions/fb32d170-3c60-4b9e-871e-a2a1f04b616b

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_first_fare_positive_of_subdiff_condition
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_with_nonnegative_first_fare

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p) :
    (∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) ∧
      IsOptimal P X f p := by
  have hf1 : 0 ≤ f 1 :=
    le_of_lt (first_fare_positive_of_subdiff_condition
      P X f p hM hp h20)
  exact theorem1_with_nonnegative_first_fare
    P X f p hM hp h20 hf1
