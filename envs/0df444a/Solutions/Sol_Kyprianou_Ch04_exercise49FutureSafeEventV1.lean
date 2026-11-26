-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49FutureSafeEventV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:59:28.83904+00:00
-- url     : https://prove2.me/submissions/f29e197f-891e-453d-96bf-f33d5a0f6ecc

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49GlobalLowerBoundRationalV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- There is a measurable path event encoding a global lower bound. -/
theorem solution
    (b : ℝ) :
    ∃ B : Set (NNReal → ℝ), MeasurableSet B ∧
      ∀ Y : NNReal → ℝ, IsCadlag Y →
        (Y ∈ B ↔ ∀ t : NNReal, b ≤ Y t) := by
  let B : Set (NNReal → ℝ) := {Y | ∀ q : ℚ, 0 < q → b ≤ Y (Real.toNNReal q)}
  refine ⟨B, ?_, ?_⟩
  · unfold B
    rw [setOf_forall]
    apply MeasurableSet.iInter
    intro q
    by_cases hq : 0 < q
    · simpa only [hq, true_implies] using
        measurableSet_le measurable_const (measurable_pi_apply (Real.toNNReal q))
    · simp [hq]
  · intro Y hY
    exact (Kyprianou.Ch04.exercise49GlobalLowerBoundRationalV1
      Y (fun t => (hY t).1) b).symm
