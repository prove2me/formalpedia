-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem2_expRevenue_prefix_policy_irrel_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T12:00:52.967561+00:00
-- url     : https://prove2.me/submissions/fdc12485-ba2d-4515-840b-0de4a6a8d707

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
theorem NestedSeatAlloc.IntPolicy.revenue_prefix_irrel_72ab1213 (f x : ℕ → ℝ) :
    ∀ (k : ℕ) (p q : ℕ → ℝ), (∀ i, i < k → p i = q i) →
      ∀ s, NestedSeatAlloc.IntPolicy.revenue f p x k s
        = NestedSeatAlloc.IntPolicy.revenue f q x k s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p q hpq s
    match k, ih, hpq with
    | 0, _, _ => simp [NestedSeatAlloc.IntPolicy.revenue]
    | 1, _, _ => simp [NestedSeatAlloc.IntPolicy.revenue]
    | m + 2, ih, hpq =>
      have hp : p (m + 1) = q (m + 1) := hpq (m + 1) (by omega)
      have hrec : ∀ t, NestedSeatAlloc.IntPolicy.revenue f p x (m + 1) t
          = NestedSeatAlloc.IntPolicy.revenue f q x (m + 1) t :=
        ih (m + 1) (by omega) p q (fun i hi => hpq i (by omega))
      simp only [NestedSeatAlloc.IntPolicy.revenue, hp, hrec]


open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (k : ℕ) (p q : ℕ → ℝ)
    (hpq : ∀ i, i < k → p i = q i) :
    ∀ s, expRevenue P X f p k s = expRevenue P X f q k s := by
  intro s
  unfold expRevenue
  congr 1
  funext ω
  exact NestedSeatAlloc.IntPolicy.revenue_prefix_irrel_72ab1213 f (fun i => X i ω) k p q
    hpq s
