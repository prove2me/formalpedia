-- Prove2me | solution 1 for ItoLemma.exists_smooth_fin_two_bump_plateau
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:53:10.40488+00:00
-- url     : https://prove2.me/submissions/45b7f92d-a96f-49fb-bbf5-7f33f437ef70

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A smooth compactly supported bump on the two-coordinate state space. -/
theorem solution
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ ψ : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) ψ ∧ HasCompactSupport ψ ∧
      (∀ z : Fin 2 → ℝ, ‖z‖ ≤ R → ψ z = 1) ∧
      (∀ z : Fin 2 → ℝ, R + 2 ≤ ‖z‖ → ψ z = 0) := by
  let bump : ContDiffBump (0 : Fin 2 → ℝ) :=
    { rIn := R + 1
      rOut := R + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨(bump : (Fin 2 → ℝ) → ℝ), bump.contDiff,
    bump.hasCompactSupport, ?_, ?_⟩
  · intro z hz
    apply bump.one_of_mem_closedBall
    change dist z 0 ≤ R + 1
    calc
      dist z 0 = ‖z‖ := dist_zero_right z
      _ ≤ R := hz
      _ ≤ R + 1 := by linarith
  · intro z hz
    apply bump.zero_of_le_dist
    change R + 2 ≤ dist z 0
    simpa only [dist_zero_right] using hz
