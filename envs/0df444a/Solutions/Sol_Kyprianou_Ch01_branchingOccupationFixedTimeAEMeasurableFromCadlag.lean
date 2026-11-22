-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOccupationFixedTimeAEMeasurableFromCadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:03:11.807111+00:00
-- url     : https://prove2.me/submissions/6a55af49-fdc4-41c0-b90f-fee6f36c14c0

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingCadlagJointMeasurableRealVersion
import Theorems.Thm_Kyprianou_Ch01_measurableRealOccupationIntervalIntegralOfJoint
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source occupation integrals inherit a.e. measurability from a jointly
measurable all-time version of the branching population. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℝ≥0 → Ω → ℕ)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∀ t : ℝ≥0,
      AEMeasurable (fun ω : Ω => branchingOccupation Y t ω) P := by
  obtain ⟨Z, hJoint, hEq⟩ :=
    Kyprianou.Ch01.branchingCadlagJointMeasurableRealVersion
      P Y hMeas hCadlag
  intro t
  have hZInt : Measurable (fun ω : Ω =>
      ∫ s in (0 : ℝ)..(t : ℝ), Z (Real.toNNReal s) ω) :=
    Kyprianou.Ch01.measurableRealOccupationIntervalIntegralOfJoint
      Z hJoint t
  apply AEMeasurable.congr hZInt.aemeasurable
  filter_upwards [hEq] with ω hω
  change (∫ s in (0 : ℝ)..(t : ℝ), Z (Real.toNNReal s) ω) =
    ∫ s in (0 : ℝ)..(t : ℝ), (Y (Real.toNNReal s) ω : ℝ)
  have hAll : (fun s : ℝ => Z (Real.toNNReal s) ω) =
      (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ)) := by
    funext s
    exact hω (Real.toNNReal s)
  rw [hAll]
