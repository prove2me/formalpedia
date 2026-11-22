-- Prove2me | solution 1 for Kyprianou.Ch01.branchingInverseOccupationAllPathMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:51:12.135117+00:00
-- url     : https://prove2.me/submissions/9a9219fa-6fe9-4e49-9a66-ed88dc635792

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_Kyprianou_Ch01_measurableRealOccupationIntervalIntegralOfJoint
import Theorems.Thm_Kyprianou_Ch01_branchingOccupationContinuousFromGlobalIntervalIntegrability
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageMeasurableOfContinuousPublic
import Theorems.Thm_Kyprianou_Ch01_inverseBranchingOccupationEqFirstUpperPassage
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- All-path càdlàg and interval integrability make the source inverse
Lamperti occupation time globally measurable at every deterministic level. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (W : ℝ≥0 → Ω → ℕ)
    (hMeas : ∀ t : ℝ≥0, Measurable (W t))
    (hCadlag : ∀ ω : Ω, IsCadlag (fun t : ℝ≥0 => W t ω))
    (hInt : ∀ (ω : Ω) (a b : ℝ),
      IntervalIntegrable
        (fun s : ℝ => (W (Real.toNNReal s) ω : ℝ)) volume a b) :
    ∀ t : ℝ≥0,
      Measurable (fun ω : Ω => inverseBranchingOccupation W t ω) := by
  have hCast : Continuous (fun n : ℕ => (n : ℝ)) :=
    continuous_of_discreteTopology
  have hJoint : Measurable (fun z : ℝ≥0 × Ω =>
      (W z.1 z.2 : ℝ)) := by
    apply AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
      (fun s ω => (W s ω : ℝ))
    · intro t
      exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (hMeas t)
    · intro ω t
      exact hCast.continuousAt.comp_continuousWithinAt
        ((hCadlag ω t).1)
  have hOcc : ∀ s : ℝ≥0,
      Measurable (fun ω : Ω => branchingOccupation W s ω) := by
    intro s
    simpa only [branchingOccupation] using
      (Kyprianou.Ch01.measurableRealOccupationIntervalIntegralOfJoint
        (fun t ω => (W t ω : ℝ)) hJoint s)
  have hCont : ∀ ω : Ω,
      Continuous (fun s : ℝ≥0 => branchingOccupation W s ω) := by
    intro ω
    exact Kyprianou.Ch01.branchingOccupationContinuousFromGlobalIntervalIntegrability
      W ω (hInt ω)
  intro t
  have hPass : Measurable (firstUpperPassage
      (fun s ω => branchingOccupation W s ω) (t : ℝ)) :=
    Kyprianou.Ch01.firstUpperPassageMeasurableOfContinuousPublic
      (fun s ω => branchingOccupation W s ω) hOcc hCont (t : ℝ)
  have hEq : (fun ω : Ω => inverseBranchingOccupation W t ω) =
      firstUpperPassage (fun s ω => branchingOccupation W s ω) (t : ℝ) := by
    funext ω
    exact Kyprianou.Ch01.inverseBranchingOccupationEqFirstUpperPassage
      W t ω
  rw [hEq]
  exact hPass
