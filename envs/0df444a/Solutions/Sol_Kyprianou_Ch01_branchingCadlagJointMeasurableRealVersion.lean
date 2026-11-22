-- Prove2me | solution 1 for Kyprianou.Ch01.branchingCadlagJointMeasurableRealVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:55:36.101887+00:00
-- url     : https://prove2.me/submissions/a06bbfe5-0b1e-4bdb-9550-25ca722f936b

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch01_measurableConullCadlagGate
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A single measurable càdlàg gate produces a jointly measurable real-valued
version of the original branching process, simultaneously at all times a.e. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℝ≥0 → Ω → ℕ)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∃ Z : ℝ≥0 → Ω → ℝ,
      Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Z t ω = (Y t ω : ℝ)) := by
  classical
  obtain ⟨G, hGmeas, hGae, hGcad⟩ :=
    Kyprianou.Ch01.measurableConullCadlagGate P Y hCadlag
  let Z : ℝ≥0 → Ω → ℝ :=
    fun t ω => if ω ∈ G then (Y t ω : ℝ) else 0
  have hCast : Continuous (fun n : ℕ => (n : ℝ)) :=
    continuous_of_discreteTopology
  have hZmeas : ∀ t : ℝ≥0, Measurable (Z t) := by
    intro t
    exact Measurable.ite hGmeas
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (hMeas t)) measurable_const
  have hZright : ∀ ω t,
      ContinuousWithinAt (fun s : ℝ≥0 => Z s ω) (Ici t) t := by
    intro ω t
    by_cases hω : ω ∈ G
    · have heq : (fun s : ℝ≥0 => Z s ω) =
          (fun s : ℝ≥0 => (Y s ω : ℝ)) := by
        funext s
        simp [Z, hω]
      rw [heq]
      exact hCast.continuousAt.comp_continuousWithinAt (hGcad ω hω t).1
    · have heq : (fun s : ℝ≥0 => Z s ω) =
          (fun _ : ℝ≥0 => (0 : ℝ)) := by
        funext s
        simp [Z, hω]
      rw [heq]
      exact continuousWithinAt_const
  have hJoint : Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2) :=
    AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
      Z hZmeas hZright
  refine ⟨Z, hJoint, ?_⟩
  filter_upwards [hGae] with ω hω
  intro t
  simp [Z, hω]
