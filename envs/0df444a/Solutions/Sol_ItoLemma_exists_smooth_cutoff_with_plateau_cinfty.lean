-- Prove2me | solution 1 for ItoLemma.exists_smooth_cutoff_with_plateau_cinfty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:35:57.87075+00:00
-- url     : https://prove2.me/submissions/47d23b47-c232-4e1f-82c1-48b751f2d55f

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-- A smooth compactly supported real cutoff equals one on a prescribed
symmetric closed interval and vanishes outside a larger interval. -/
theorem solution
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : ℝ → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) φ ∧ HasCompactSupport φ ∧
      (∀ x : ℝ, |x| ≤ R → φ x = 1) ∧
      (∀ x : ℝ, R + 2 ≤ |x| → φ x = 0) := by
  let bump : ContDiffBump (0 : ℝ) :=
    { rIn := R + 1
      rOut := R + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨(bump : ℝ → ℝ), bump.contDiff, bump.hasCompactSupport, ?_, ?_⟩
  · intro x hx
    apply bump.one_of_mem_closedBall
    change dist x 0 ≤ R + 1
    calc
      dist x 0 = |x| := by simp [Real.dist_eq]
      _ ≤ R := hx
      _ ≤ R + 1 := by linarith
  · intro x hx
    apply bump.zero_of_le_dist
    change R + 2 ≤ dist x 0
    calc
      R + 2 ≤ |x| := hx
      _ = dist x 0 := by simp [Real.dist_eq]
