-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.stoppedRationalCutoffGapNullMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:42:26.486579+00:00
-- url     : https://prove2.me/submissions/4315824e-60ab-4f1b-af3f-0a383a1fb2e6

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_rationalPrefixUniformGapNullMeasurable
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
    ∀ q : ℚ,
      NullMeasurableSet
        {ω : Ω | 0 ≤ q →
          ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
          ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
            f (r : ℝ).toNNReal ω <
              h - 1 / (((n + 1 : ℕ) : ℝ))} P := by
  intro q
  by_cases hq : 0 ≤ q
  · have hTq : NullMeasurableSet
        {ω : Ω | ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω} P := by
      exact hT.nullMeasurableSet_preimage
        (measurableSet_Ioi : MeasurableSet
          (Set.Ioi ((q : ℝ).toNNReal : WithTop ℝ≥0)))
    have hn : NullMeasurableSet
        {ω : Ω | ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
          f (r : ℝ).toNNReal ω <
            h - 1 / (((n + 1 : ℕ) : ℝ))} P := by
      rw [show
        {ω : Ω | ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
          f (r : ℝ).toNNReal ω <
            h - 1 / (((n + 1 : ℕ) : ℝ))} =
        ⋃ n : ℕ, {ω : Ω | ∀ r : ℚ, 0 ≤ r → r ≤ q →
          f (r : ℝ).toNNReal ω <
            h - 1 / (((n + 1 : ℕ) : ℝ))} by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]]
      exact NullMeasurableSet.iUnion
        (fun n => Kyprianou.Ch08.StageB.rationalPrefixUniformGapNullMeasurable
          P f h hf q n)
    have heq :
        {ω : Ω | ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
          ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
            f (r : ℝ).toNNReal ω <
              h - 1 / (((n + 1 : ℕ) : ℝ))} =
        ({ω : Ω | ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω})ᶜ ∪
        {ω : Ω | ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
          f (r : ℝ).toNNReal ω <
            h - 1 / (((n + 1 : ℕ) : ℝ))} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      tauto
    have hImpl : NullMeasurableSet
        {ω : Ω | ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
          ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
            f (r : ℝ).toNNReal ω <
              h - 1 / (((n + 1 : ℕ) : ℝ))} P := by
      rw [heq]
      exact hTq.compl.union hn
    simpa only [hq, true_implies] using hImpl
  · simp [hq]
