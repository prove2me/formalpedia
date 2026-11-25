-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteJumpAfterMaxAffineV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:15:57.268426+00:00
-- url     : https://prove2.me/submissions/33a27ebb-c3e0-4801-8ee6-0b63ee29e4ad

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k) (u : ℝ) (hu : τ k ≤ u) :
    a + d * u + ∑ s ∈ insert k S, (if τ s ≤ u then j s else 0) =
      (a + ∑ s ∈ insert k S, j s) + d * u := by
  classical
  have hsum : (∑ s ∈ insert k S, if τ s ≤ u then j s else 0) =
      ∑ s ∈ insert k S, j s := by
    apply Finset.sum_congr rfl
    intro s hs
    have hsu : τ s ≤ u := by
      rcases Finset.mem_insert.mp hs with rfl | hs'
      · exact hu
      · exact (hτ (hk s hs')).le.trans hu
    simp [hsu]
  rw [hsum]
  ring
