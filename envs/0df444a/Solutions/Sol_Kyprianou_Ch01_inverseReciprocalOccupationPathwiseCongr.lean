-- Prove2me | solution 1 for Kyprianou.Ch01.inverseReciprocalOccupationPathwiseCongr
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T16:10:19.774979+00:00
-- url     : https://prove2.me/submissions/48caf8bb-fd64-4029-9374-dbcca7d2bfa5

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (W X : ℝ≥0 → Ω → ℤ) (w : Ω)
    (hPath : ∀ s : ℝ≥0, W s w = X s w) (v : ℝ≥0) :
    inverseReciprocalOccupation W v w =
      inverseReciprocalOccupation X v w := by
  have hOcc (s : ℝ≥0) :
      reciprocalOccupation W s w = reciprocalOccupation X s w := by
    simp only [reciprocalOccupation, hPath]
  have hExists :
      (∃ s : ℝ≥0, (v : ℝ≥0∞) < reciprocalOccupation W s w) =
      (∃ s : ℝ≥0, (v : ℝ≥0∞) < reciprocalOccupation X s w) := by
    apply propext
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, by simpa only [hOcc s] using hs⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, by simpa only [hOcc s] using hs⟩
  have hSet :
      {s : ℝ≥0 | (v : ℝ≥0∞) < reciprocalOccupation W s w} =
      {s : ℝ≥0 | (v : ℝ≥0∞) < reciprocalOccupation X s w} := by
    ext s
    change ((v : ℝ≥0∞) < reciprocalOccupation W s w) ↔
      ((v : ℝ≥0∞) < reciprocalOccupation X s w)
    rw [hOcc s]
  unfold inverseReciprocalOccupation
  rw [hExists, hSet]
