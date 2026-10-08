-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem2_integer_subdiff_policy_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T07:15:24.66144+00:00
-- url     : https://prove2.me/submissions/69531d75-819a-4451-ab7b-ba6cdd3ded8d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_integer_base_step
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_prefix_extension_bridge
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_policy_assembly

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ p : ℕ → ℕ, SubdiffCondition P X f (fun k => (p k : ℝ)) := by
  apply theorem2_policy_assembly P X f hM
  · intro k p hk h20 hclbi
    exact theorem2_prefix_extension_bridge P X f k p hM hint hpos hk hclbi h20
  · exact theorem2_integer_base_step P X f hM hint hpos
