-- Prove2me | solution 1 for Kyprianou.Ch01.measurableInverseReciprocalOccupationFromSections
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:08:38.183878+00:00
-- url     : https://prove2.me/submissions/febc5a7f-eb4e-4c67-a617-3bf86de744b6

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
    ∀ t : ℝ≥0,
      Measurable (fun ω : Ω => inverseReciprocalOccupation X t ω) := by
  intro t
  have hEq : (fun ω : Ω => inverseReciprocalOccupation X t ω) =
      (fun ω : Ω =>
        ⨅ q : ℚ,
          if (0 < (q : ℝ) ∧
              (t : ℝ≥0∞) <
                reciprocalOccupation X (Real.toNNReal (q : ℝ)) ω)
            then ((Real.toNNReal (q : ℝ)) : WithTop ℝ≥0)
            else ⊤) := by
    funext ω
    exact Kyprianou.Ch01.inverseReciprocalOccupationRationalInf X ω t
  rw [hEq]
  classical
  apply Measurable.iInf
  intro q
  have hp : MeasurableSet
      {ω : Ω | 0 < (q : ℝ) ∧
        (t : ℝ≥0∞) < reciprocalOccupation X (Real.toNNReal (q : ℝ)) ω} := by
    by_cases hq : 0 < (q : ℝ)
    · simp only [hq, true_and]
      exact measurableSet_Ioi.preimage (hMeas _)
    · simp only [hq, false_and]
      exact MeasurableSet.empty
  exact Measurable.ite hp measurable_const measurable_const
