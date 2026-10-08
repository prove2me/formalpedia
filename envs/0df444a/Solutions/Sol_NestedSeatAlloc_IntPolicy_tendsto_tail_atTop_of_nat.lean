-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.tendsto_tail_atTop_of_nat
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:27:10.954735+00:00
-- url     : https://prove2.me/submissions/388e5936-2e0d-4f22-9ea6-8dbe1d0eea05

import Mathlib

open Filter
open scoped Topology

namespace NestedSeatAlloc.IntPolicy

open Filter
open scoped Topology

theorem tendsto_tail_atTop_of_nat
    (tail : ℝ → ℝ)
    (hanti : Antitone tail)
    (hnonneg : ∀ x, 0 ≤ tail x)
    (hseq : Tendsto (fun n : ℕ => tail (n : ℝ)) atTop (𝓝 0)) :
    Tendsto tail atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun x => lt_of_lt_of_le ha (hnonneg x))
  · intro b hb
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hseq).2 b hb)
    filter_upwards [Filter.eventually_ge_atTop (N : ℝ)] with x hx
    exact lt_of_le_of_lt (hanti hx) (hN N le_rfl)

end NestedSeatAlloc.IntPolicy

theorem solution
    (tail : ℝ → ℝ)
    (hanti : Antitone tail)
    (hnonneg : ∀ x, 0 ≤ tail x)
    (hseq : Tendsto (fun n : ℕ => tail (n : ℝ)) atTop (𝓝 0)) :
    Tendsto tail atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun x => lt_of_lt_of_le ha (hnonneg x))
  · intro b hb
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hseq).2 b hb)
    filter_upwards [Filter.eventually_ge_atTop (N : ℝ)] with x hx
    exact lt_of_le_of_lt (hanti hx) (hN N le_rfl)

#print axioms solution

