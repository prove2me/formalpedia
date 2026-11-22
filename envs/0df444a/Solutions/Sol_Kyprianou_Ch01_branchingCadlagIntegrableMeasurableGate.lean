-- Prove2me | solution 1 for Kyprianou.Ch01.branchingCadlagIntegrableMeasurableGate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:51:00.474707+00:00
-- url     : https://prove2.me/submissions/1f9885b6-e6ad-4f99-96fb-149c40d084bb

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_measurableConullCadlagGate
import Theorems.Thm_Kyprianou_Ch01_cadlagNaturalPopulationGloballyIntervalIntegrable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Gate the branching process on one measurable conull càdlàg event;
every gated path is càdlàg and hence interval-integrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => Y t ω))
    (hInt : ∀ᵐ ω ∂P, ∀ a b : ℝ,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ)) volume a b) :
    ∃ W : ℝ≥0 → Ω → ℕ,
      (∀ t : ℝ≥0, Measurable (W t)) ∧
      (∀ ω : Ω, IsCadlag (fun t : ℝ≥0 => W t ω)) ∧
      (∀ (ω : Ω) (a b : ℝ),
        IntervalIntegrable
          (fun s : ℝ => (W (Real.toNNReal s) ω : ℝ)) volume a b) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, W t ω = Y t ω) := by
  classical
  obtain ⟨G, hGmeas, hGae, hGcad⟩ :=
    Kyprianou.Ch01.measurableConullCadlagGate P Y hCadlag
  let W : ℝ≥0 → Ω → ℕ := fun t ω => if ω ∈ G then Y t ω else 0
  have hWMeas : ∀ t : ℝ≥0, Measurable (W t) := by
    intro t
    exact Measurable.ite hGmeas (hMeas t) measurable_const
  have hWCad : ∀ ω : Ω, IsCadlag (fun t : ℝ≥0 => W t ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [W, if_pos hω] using hGcad ω hω
    · have hzero : (fun t : ℝ≥0 => W t ω) =
          (fun _ : ℝ≥0 => (0 : ℕ)) := by
        funext t
        simp [W, hω]
      rw [hzero]
      intro t
      exact ⟨continuousWithinAt_const, ⟨0, tendsto_const_nhds⟩⟩
  refine ⟨W, hWMeas, hWCad, ?_, ?_⟩
  · intro ω a b
    exact Kyprianou.Ch01.cadlagNaturalPopulationGloballyIntervalIntegrable
      W ω (hWCad ω) a b
  · filter_upwards [hGae] with ω hω
    intro t
    simp [W, hω]
