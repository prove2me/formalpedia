-- Prove2me | solution 1 for Kyprianou.Ch01.smallPassageAeOfArbitrarilySmallTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:22:28.152188+00:00
-- url     : https://prove2.me/submissions/d3070ba5-39ce-4030-9b23-6efac1b49a96

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_nullEventOfArbitrarilySmallOuterBoundsV1
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0)
    (hSmall : ∀ δ : ℝ, 0 < δ →
      ∃ s : ℝ≥0, 0 < s ∧
      (P {ω | (ε : WithTop ℝ≥0) ≤
         firstUpperPassage X (s : ℝ) ω}).toReal < δ) :
    ∀ᵐ ω ∂P, ∃ s : ℝ≥0, 0 < s ∧
      firstUpperPassage X (s : ℝ) ω <
        (ε : WithTop ℝ≥0) := by
  let E : Set Ω :=
    {ω | ¬∃ s : ℝ≥0, 0 < s ∧
      firstUpperPassage X (s : ℝ) ω <
        (ε : WithTop ℝ≥0)}
  let A : {s : ℝ≥0 // 0 < s} → Set Ω :=
    fun s => {ω | (ε : WithTop ℝ≥0) ≤
       firstUpperPassage X (s.val : ℝ) ω}
  have hSub : ∀ i, E ⊆ A i := by
    intro i ω hBad
    by_contra hi
    exact hBad ⟨i.val, i.property, lt_of_not_ge hi⟩
  have hSmallA : ∀ δ : ℝ, 0 < δ →
      ∃ i : {s : ℝ≥0 // 0 < s}, (P (A i)).toReal < δ := by
    intro δ hδ
    obtain ⟨s, hs, hle⟩ := hSmall δ hδ
    exact ⟨⟨s, hs⟩, hle⟩
  have hNull : P E = 0 :=
    nullEventOfArbitrarilySmallOuterBoundsV1 P E A hSub hSmallA
  exact (ae_iff).2 hNull
