-- Prove2me | solution 1 for Kyprianou.Ch01.branchingInverseOccupationMeasurablePathFromIntegrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:49:40.793803+00:00
-- url     : https://prove2.me/submissions/f6b78355-400c-4740-a5b9-4f72f75705bd

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Theorems.Thm_Kyprianou_Ch01_branchingCadlagIntegrableMeasurableGate
import Theorems.Thm_Kyprianou_Ch01_branchingInverseOccupationAllPathMeasurable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A single conull all-path regularisation supplies a globally measurable
inverse-clock version identical to the source at all levels. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => Y t ω))
    (hInt : ∀ᵐ ω ∂P, ∀ a b : ℝ,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume a b) :
    ∃ C : ℝ≥0 → Ω → WithTop ℝ≥0,
      (∀ t : ℝ≥0, Measurable (C t)) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        C t ω = inverseBranchingOccupation Y t ω := by
  classical
  obtain ⟨W, hWMeas, hWCad, hWInt, hWEq⟩ :=
    Kyprianou.Ch01.branchingCadlagIntegrableMeasurableGate
      Y P hMeas hCadlag hInt
  have hClock : ∀ t : ℝ≥0,
      Measurable (fun ω : Ω => inverseBranchingOccupation W t ω) :=
    Kyprianou.Ch01.branchingInverseOccupationAllPathMeasurable
      W hWMeas hWCad hWInt
  refine ⟨(fun t ω => inverseBranchingOccupation W t ω), hClock, ?_⟩
  filter_upwards [hWEq] with ω hω
  intro t
  have hOccupation : ∀ s : ℝ≥0,
      branchingOccupation W s ω = branchingOccupation Y s ω := by
    intro s
    unfold branchingOccupation
    congr 1
    funext r
    exact congrArg (fun n : ℕ => (n : ℝ))
      (hω (Real.toNNReal r))
  simp only [inverseBranchingOccupation, hOccupation]
