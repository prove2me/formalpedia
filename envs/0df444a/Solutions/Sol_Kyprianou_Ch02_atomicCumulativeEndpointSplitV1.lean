-- Prove2me | solution 1 for Kyprianou.Ch02.atomicCumulativeEndpointSplitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:29:08.742963+00:00
-- url     : https://prove2.me/submissions/a73f61f5-c9a8-45ad-919f-c8fc5efacfcc

import Mathlib.Analysis.Normed.Group.InfiniteSum
open Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (F : ℝ≥0 → ℝ) (hS : Summable (fun u : ℝ≥0 => |F u|))
    (t : ℝ≥0) (ht : 0 < t) :
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then F u else 0) =
      (∑' u : ℝ≥0, if 0 < u ∧ u < t then F u else 0) + F t := by
  classical
  let L : ℝ≥0 → ℝ := fun u => if 0 < u ∧ u < t then F u else 0
  let A : ℝ≥0 → ℝ := fun u => if u = t then F u else 0
  have hL : Summable L := by
    apply hS.of_norm_bounded
    intro u
    dsimp [L]
    split_ifs <;> simp [Real.norm_eq_abs, abs_nonneg]
  have hA : Summable A := by
    apply hS.of_norm_bounded
    intro u
    dsimp [A]
    split_ifs <;> simp [Real.norm_eq_abs, abs_nonneg]
  have hsplit : (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then F u else 0) =
      (∑' u, L u) + F t := by
    rw [← tsum_ite_eq t F, ← hL.tsum_add hA]
    apply tsum_congr
    intro u
    by_cases hut : u = t
    · subst u
      simp [L, A, ht]
    · by_cases hu : u < t
      · simp [L, A, hut, hu, hu.le]
      · have hnot : ¬ u ≤ t := fun h => hut (le_antisymm h (le_of_not_gt hu))
        simp [L, A, hut, hu, hnot]
  exact hsplit
