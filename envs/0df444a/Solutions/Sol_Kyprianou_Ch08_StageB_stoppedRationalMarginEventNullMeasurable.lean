-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.stoppedRationalMarginEventNullMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:42:36.152738+00:00
-- url     : https://prove2.me/submissions/a727b764-b033-496e-b032-7a7122313193

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_stoppedRationalCutoffGapNullMeasurable
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (h : ℝ)
    (hT : AEMeasurable T P)
    (hf : ∀ r : ℚ, 0 ≤ r →
      AEMeasurable (f (r : ℝ).toNNReal) P) :
    NullMeasurableSet
      {ω : Ω |
        ∀ q : ℚ, 0 ≤ q →
          ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
          ∃ n : ℕ,
            ∀ r : ℚ, 0 ≤ r → r ≤ q →
              f (r : ℝ).toNNReal ω <
                h - 1 / (((n + 1 : ℕ) : ℝ))} P := by
  have heq :
      {ω : Ω |
        ∀ q : ℚ, 0 ≤ q →
          ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
          ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
            f (r : ℝ).toNNReal ω <
              h - 1 / (((n + 1 : ℕ) : ℝ))} =
      ⋂ q : ℚ, {ω : Ω | 0 ≤ q →
        ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
        ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
          f (r : ℝ).toNNReal ω <
            h - 1 / (((n + 1 : ℕ) : ℝ))} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  exact NullMeasurableSet.iInter
    (Kyprianou.Ch08.StageB.stoppedRationalCutoffGapNullMeasurable
      P f T h hT hf)
