-- Prove2me | solution 1 for Kyprianou.Ch01.measurableJointInverseReciprocalOccupationFromSections
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:48:40.443547+00:00
-- url     : https://prove2.me/submissions/61466ca9-0e33-4b19-a8eb-c55918f52464

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationRationalInf
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hMeas : ∀ s : ℝ≥0,
      Measurable (fun ω : Ω => reciprocalOccupation X s ω)) :
    Measurable (fun z : ℝ≥0 × Ω =>
      inverseReciprocalOccupation X z.1 z.2) := by
  have hEq :
      (fun z : ℝ≥0 × Ω =>
        inverseReciprocalOccupation X z.1 z.2) =
      (fun z : ℝ≥0 × Ω =>
        ⨅ q : ℚ,
          if (0 < (q : ℝ) ∧
              (z.1 : ℝ≥0∞) <
                reciprocalOccupation X (Real.toNNReal (q : ℝ)) z.2)
          then ((Real.toNNReal (q : ℝ)) : WithTop ℝ≥0)
          else ⊤) := by
    funext z
    exact Kyprianou.Ch01.inverseReciprocalOccupationRationalInf X z.2 z.1
  rw [hEq]
  classical
  apply Measurable.iInf
  intro q
  have hLeft : Measurable
      (fun z : ℝ≥0 × Ω => (z.1 : ℝ≥0∞)) := by
    fun_prop
  have hRight : Measurable
      (fun z : ℝ≥0 × Ω =>
        reciprocalOccupation X (Real.toNNReal (q : ℝ)) z.2) :=
    (hMeas _).comp measurable_snd
  have hp : MeasurableSet
      {z : ℝ≥0 × Ω |
        0 < (q : ℝ) ∧
        (z.1 : ℝ≥0∞) <
          reciprocalOccupation X (Real.toNNReal (q : ℝ)) z.2} := by
    by_cases hq : 0 < (q : ℝ)
    · simp only [hq, true_and]
      exact measurableSet_lt hLeft hRight
    · simp only [hq, false_and]
      exact MeasurableSet.empty
  exact Measurable.ite hp measurable_const measurable_const
