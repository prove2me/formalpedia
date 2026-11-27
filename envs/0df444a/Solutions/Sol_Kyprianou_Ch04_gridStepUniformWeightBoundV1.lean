-- Prove2me | solution 1 for Kyprianou.Ch04.gridStepUniformWeightBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:38:43.44621+00:00
-- url     : https://prove2.me/submissions/7a763726-8bcc-4891-99ae-87c1e43e0fde

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- Disjoint right-closed monotone grid cells preserve a uniform weight bound,
including points outside the grid. -/
theorem solution {Ω : Type} (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (H : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ k ∈ Finset.range n, ∀ w, |H k w| ≤ K) :
    ∀ s w, |∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
      (fun _ => H k w) s| ≤ K := by
  intro s w
  by_cases he : ∃ k ∈ Finset.range n, s ∈ Ioc (u k) (u (k+1))
  · obtain ⟨k,hk,hs⟩ := he
    rw [Finset.sum_eq_single k]
    · simpa [Set.indicator_of_mem hs] using hH k hk w
    · intro i hi hik
      apply Set.indicator_of_notMem
      intro hi'
      rcases lt_or_gt_of_ne hik with hlt | hgt
      · exact (not_lt_of_ge (hi'.2.trans (hu (by omega : i+1 ≤ k)))) hs.1
      · exact (not_lt_of_ge (hs.2.trans (hu (by omega : k+1 ≤ i)))) hi'.1
    · exact fun h => (h hk).elim
  · have hz : ∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
        (fun _ => H k w) s = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact Set.indicator_of_notMem (fun hs => he ⟨k,hk,hs⟩) _
    rw [hz,abs_zero]
    exact hK
