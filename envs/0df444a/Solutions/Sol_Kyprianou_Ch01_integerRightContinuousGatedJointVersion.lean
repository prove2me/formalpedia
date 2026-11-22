-- Prove2me | solution 1 for Kyprianou.Ch01.integerRightContinuousGatedJointVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:02:08.477836+00:00
-- url     : https://prove2.me/submissions/f0bf5b23-fea8-4bbb-9351-5b0dc842f621

import Mathlib
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Gate to zero off a measurable right-continuous set, then use the
proved joint-measurable real process and exact integer floor. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℤ)
    (hF : ∀ t : ℝ≥0, Measurable (F t))
    (G : Set Ω) (hG : MeasurableSet G)
    (hRight : ∀ ω ∈ G, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t) :
    ∃ W : ℝ≥0 → Ω → ℤ,
      Measurable (fun z : ℝ≥0 × Ω => W z.1 z.2) ∧
      ∀ ω ∈ G, ∀ t : ℝ≥0, W t ω = F t ω := by
  classical
  let W : ℝ≥0 → Ω → ℤ := fun t ω => if ω ∈ G then F t ω else 0
  have hWmeas : ∀ t : ℝ≥0, Measurable (W t) := by
    intro t
    change Measurable (fun ω : Ω => if ω ∈ G then F t ω else (0 : ℤ))
    exact Measurable.ite hG (hF t) measurable_const
  have hCast : Continuous (fun z : ℤ => (z : ℝ)) :=
    continuous_of_discreteTopology
  have hWrc : ∀ ω t, ContinuousWithinAt
      (fun s : ℝ≥0 => (W s ω : ℝ)) (Set.Ici t) t := by
    intro ω t
    by_cases hω : ω ∈ G
    · simpa only [W, if_pos hω, Function.comp_def] using
        hCast.continuousAt.comp_continuousWithinAt (hRight ω hω t)
    · have hzero : (fun s : ℝ≥0 => (W s ω : ℝ)) =
          fun _ => (0 : ℝ) := by
        funext s
        simp [W, hω]
      rw [hzero]
      exact continuousWithinAt_const
  have hReal : Measurable (fun z : ℝ≥0 × Ω =>
      (W z.1 z.2 : ℝ)) :=
    AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
      (fun s ω => (W s ω : ℝ))
      (fun t => hCast.measurable.comp (hWmeas t)) hWrc
  have hJoint : Measurable (fun z : ℝ≥0 × Ω =>
      W z.1 z.2) := by
    simpa only [Function.comp_def, Int.floor_intCast] using
      (Int.measurable_floor.comp hReal)
  exact ⟨W, hJoint, by intro ω hω t; simp [W, hω]⟩
