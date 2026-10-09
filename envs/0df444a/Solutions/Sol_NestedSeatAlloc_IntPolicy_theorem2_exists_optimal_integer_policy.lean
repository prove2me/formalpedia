-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem2_exists_optimal_integer_policy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:01:51.148983+00:00
-- url     : https://prove2.me/submissions/5526649b-edef-4e75-b22b-07e807e6c5c4

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_integer_subdiff_policy_exists
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_subdiff_condition_optimal

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ p : ℕ → ℕ, IsOptimal P X f (fun k => (p k : ℝ)) ∧
      SubdiffCondition P X f (fun k => (p k : ℝ)) := by
  obtain ⟨p, h20⟩ := theorem2_integer_subdiff_policy_exists P X f hM hint hpos
  have hp : IsProtectionPolicy (fun k => (p k : ℝ)) := by
    intro k hk
    change (0 : ℝ) ≤ (p k : ℝ)
    exact_mod_cast Nat.zero_le (p k)
  have hopt := theorem1_subdiff_condition_optimal P X f (fun k => (p k : ℝ)) hM hp h20
  exact ⟨p, hopt.2, h20⟩
