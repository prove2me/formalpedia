-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49FuturePrefixEventV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:59:28.883965+00:00
-- url     : https://prove2.me/submissions/f9749664-43cd-41db-a705-f7e134e0bffa

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49PrefixLowerBoundRationalV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- There is a measurable path event encoding the nonnegative prefix and endpoint gain. -/
theorem solution
    (s : NNReal) (b : ℝ) :
    ∃ B : Set (NNReal → ℝ), MeasurableSet B ∧
      ∀ Y : NNReal → ℝ, IsCadlag Y →
        (Y ∈ B ↔ (∀ t : NNReal, t ≤ s → 0 ≤ Y t) ∧ b ≤ Y s) := by
  let B : Set (NNReal → ℝ) := {Y |
    (0 ≤ Y s ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < s →
      0 ≤ Y (Real.toNNReal q)) ∧ b ≤ Y s}
  refine ⟨B, ?_, ?_⟩
  · have hR : MeasurableSet {Y : NNReal → ℝ |
        ∀ q : ℚ, 0 < q → (q : ℝ) < s → 0 ≤ Y (Real.toNNReal q)} := by
      rw [setOf_forall]
      apply MeasurableSet.iInter
      intro q
      by_cases hq : 0 < q
      · by_cases hqs : (q : ℝ) < s
        · simpa only [hq, hqs, true_implies] using
            measurableSet_le measurable_const (measurable_pi_apply (Real.toNNReal q))
        · simp [hqs]
      · simp [hq]
    exact (measurableSet_le measurable_const (measurable_pi_apply s)).inter hR |>.inter
      (measurableSet_le measurable_const (measurable_pi_apply s))
  · intro Y hY
    exact and_congr (Kyprianou.Ch04.exercise49PrefixLowerBoundRationalV1
      Y (fun t => (hY t).1) s 0).symm Iff.rfl
