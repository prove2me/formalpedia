-- Prove2me | solution 1 for Kyprianou.Ch01.cadlagNaturalPopulationMeasurableAndCompactBounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:53:08.801126+00:00
-- url     : https://prove2.me/submissions/1f637cde-74cc-4b11-b1c1-0f3faf2de9f3

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The measurable real-time extension of a càdlàg population path is
bounded on each finite nonnegative horizon. -/
theorem solution
    {Ω : Type*}
    (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hCadlag : IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    Measurable (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ)) ∧
    ∀ T : ℝ≥0, ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℝ≥0, s ≤ T → (Y s ω : ℝ) ≤ M := by
  have hCast : Continuous (fun n : ℕ => (n : ℝ)) :=
    continuous_of_discreteTopology
  have hf : IsCadlag (fun t : ℝ≥0 => (Y t ω : ℝ)) := by
    intro t
    obtain ⟨hr, l, hl⟩ := hCadlag t
    exact ⟨hCast.continuousAt.comp_continuousWithinAt hr,
      ⟨(l : ℝ), hCast.continuousAt.tendsto.comp hl⟩⟩
  have hJoint : Measurable (fun z : ℝ≥0 × Unit => (Y z.1 ω : ℝ)) :=
    AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
      (fun t (_ : Unit) => (Y t ω : ℝ))
      (fun _ => measurable_const) (fun _ t => (hf t).1)
  have hPair : Measurable
      (fun t : ℝ≥0 => (t, ((): Unit))) :=
    measurable_id.prodMk measurable_const
  have hNN : Measurable (fun t : ℝ≥0 => (Y t ω : ℝ)) := by
    have hEval : Measurable (fun t : ℝ≥0 =>
        (Y ((t, ((): Unit)) : ℝ≥0 × Unit).1 ω : ℝ)) :=
      hJoint.comp hPair
    simpa using hEval
  have hReal : Measurable
      (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ)) :=
    hNN.comp measurable_real_toNNReal
  refine ⟨hReal, ?_⟩
  intro T
  obtain ⟨M, hM⟩ :=
    Kyprianou.Ch01.cadlag_runningSup_bddAbove
      (fun t : ℝ≥0 => (Y t ω : ℝ)) hf T
  have hB : ∀ s : ℝ≥0, s ≤ T → (Y s ω : ℝ) ≤ M := by
    intro s hs
    exact hM ⟨s, hs, rfl⟩
  have hM0 : 0 ≤ M := by
    have h0 : (Y 0 ω : ℝ) ≤ M := hB 0 (zero_le)
    exact (Nat.cast_nonneg _).trans h0
  exact ⟨M, hM0, hB⟩
