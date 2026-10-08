-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem2_expRevenue_prefix_policy_irrel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:20:12.372996+00:00
-- url     : https://prove2.me/submissions/7aca0a6d-f152-4c50-a11f-9bae53308b69

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
theorem NestedSeatAlloc.IntPolicy.revenue_prefix_irrel_48cd0208 (f x : ℕ → ℝ) :
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
    (hpq : ∀ i, i ≤ k → p i = q i) :
    ∀ s, expRevenue P X f p k s = expRevenue P X f q k s := by
  intro s
  unfold expRevenue
  congr 1
  funext ω
  exact NestedSeatAlloc.IntPolicy.revenue_prefix_irrel_48cd0208 f (fun i => X i ω) k p q
    (fun i hi => hpq i (le_of_lt hi)) s
