-- Prove2me | solution 1 for ItoLemma.exists_smooth_identity_saturation_cinfty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:35:54.297688+00:00
-- url     : https://prove2.me/submissions/ee807fb8-6987-4e05-bcef-4abd5198e7e3

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-- A compactly supported smooth scalar function agrees with the identity
on any prescribed symmetric bounded interval. -/
theorem solution
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ρ ∧ HasCompactSupport ρ ∧
      ∀ x : ℝ, |x| ≤ R → ρ x = x := by
  let bump : ContDiffBump (0 : ℝ) :=
    { rIn := R + 1
      rOut := R + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨(fun x : ℝ => (bump : ℝ → ℝ) x * x), ?_, ?_, ?_⟩
  · exact bump.contDiff.mul contDiff_id
  · change HasCompactSupport ((bump : ℝ → ℝ) * (fun x : ℝ => x))
    exact bump.hasCompactSupport.mul_right
  · intro x hx
    have hin : x ∈ Metric.closedBall (0 : ℝ) bump.rIn := by
      change dist x 0 ≤ R + 1
      calc
        dist x 0 = |x| := by simp [Real.dist_eq]
        _ ≤ R := hx
        _ ≤ R + 1 := by linarith
    have hone : (bump : ℝ → ℝ) x = 1 :=
      bump.one_of_mem_closedBall hin
    simp [hone]
