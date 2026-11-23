-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.rationalPrefixUniformGapNullMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:42:18.276734+00:00
-- url     : https://prove2.me/submissions/772896cd-c37d-430f-8176-121d0b8b839b

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ≥0 → Ω → ℝ)
    (h : ℝ)
    (hf : ∀ r : ℚ, 0 ≤ r →
      AEMeasurable (f (r : ℝ).toNNReal) P) :
    ∀ (q : ℚ) (n : ℕ),
      NullMeasurableSet
        {ω : Ω | ∀ r : ℚ, 0 ≤ r → r ≤ q →
          f (r : ℝ).toNNReal ω <
            h - 1 / (((n + 1 : ℕ) : ℝ))} P := by
  intro q n
  have heq :
      {ω : Ω | ∀ r : ℚ, 0 ≤ r → r ≤ q →
        f (r : ℝ).toNNReal ω <
          h - 1 / (((n + 1 : ℕ) : ℝ))} =
      ⋂ r : ℚ, {ω : Ω | 0 ≤ r → r ≤ q →
        f (r : ℝ).toNNReal ω <
          h - 1 / (((n + 1 : ℕ) : ℝ))} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  apply NullMeasurableSet.iInter
  intro r
  by_cases hr : 0 ≤ r
  · by_cases hrq : r ≤ q
    · have hlevel : NullMeasurableSet
          {ω : Ω |
            f (r : ℝ).toNNReal ω <
              h - 1 / (((n + 1 : ℕ) : ℝ))} P := by
        exact (hf r hr).nullMeasurableSet_preimage
          (measurableSet_Iio : MeasurableSet
            (Set.Iio (h - 1 / (((n + 1 : ℕ) : ℝ)))))
      simpa only [hr, hrq, true_implies] using hlevel
    · simp [hrq]
  · simp [hr]
