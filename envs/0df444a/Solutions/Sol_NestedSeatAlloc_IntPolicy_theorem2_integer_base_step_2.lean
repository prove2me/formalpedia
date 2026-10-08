-- Prove2me | solution 2 for NestedSeatAlloc.IntPolicy.theorem2_integer_base_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:11:26.496998+00:00
-- url     : https://prove2.me/submissions/230305cb-0477-4476-943a-252f13996e9e

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI
import Theorems.Thm_NestedSeatAlloc_IntPolicy_eq27_er1_clbi
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_covering
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_base_tail_bound_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ n : ℕ, InSubdiff (expRevenue P X f (fun j => (n : ℝ)) 1) n (f 2) := by
  have hf1 : 0 ≤ f 1 := le_of_lt (hpos 1 (by norm_num))
  obtain ⟨hclbi, _, _⟩ :=
    eq27_er1_clbi P X f (fun _ => (0 : ℝ)) hM hint hf1
  obtain ⟨s, hs, r, hr, hrf⟩ :=
    theorem2_base_tail_bound_positive P X f (fun _ => (0 : ℝ)) hM hint hpos
  obtain ⟨n, _, _, hn⟩ :=
    clbi_covering (expRevenue P X f (fun _ => (0 : ℝ)) 1) hclbi 0 s (f 2)
      (by norm_num) hs ⟨r, hr, hrf⟩ (Or.inl rfl)
  exact ⟨n, hn⟩
