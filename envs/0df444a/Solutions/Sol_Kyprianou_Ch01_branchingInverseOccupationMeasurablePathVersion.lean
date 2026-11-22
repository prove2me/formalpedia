-- Prove2me | solution 1 for Kyprianou.Ch01.branchingInverseOccupationMeasurablePathVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:37:07.715556+00:00
-- url     : https://prove2.me/submissions/6b3c334b-10e5-429c-ae78-f3821c4de51a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch01_cadlagNaturalPopulationGloballyIntervalIntegrable
import Theorems.Thm_Kyprianou_Ch01_branchingInverseOccupationMeasurablePathFromIntegrability
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Almost-sure càdlàg branching paths provide global interval-integrability
on a conull event and thereby measurable inverse occupation clocks. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∃ C : ℝ≥0 → Ω → WithTop ℝ≥0,
      (∀ t : ℝ≥0, Measurable (C t)) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        C t ω = inverseBranchingOccupation Y t ω := by
  have hInt : ∀ᵐ ω ∂P, ∀ a b : ℝ,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume a b := by
    filter_upwards [hCadlag] with ω hω
    exact Kyprianou.Ch01.cadlagNaturalPopulationGloballyIntervalIntegrable
      Y ω hω
  exact Kyprianou.Ch01.branchingInverseOccupationMeasurablePathFromIntegrability
    Y P hMeas hCadlag hInt
