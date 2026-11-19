-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassageBarrierMonotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:16:39.816213+00:00
-- url     : https://prove2.me/submissions/c3a7580e-4f98-4493-bb26-6c5f4963368a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict first-upper-passage times increase with the barrier, including non-hitting paths. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (a b : ℝ) (hab : a ≤ b) (ω : Ω) :
    firstUpperPassage X a ω ≤ firstUpperPassage X b ω := by
  classical
  by_cases hb : ∃ t : ℝ≥0, 0 < t ∧ b < X t ω
  · have ha : ∃ t : ℝ≥0, 0 < t ∧ a < X t ω := by
      obtain ⟨t, ht, hcross⟩ := hb
      exact ⟨t, ht, lt_of_le_of_lt hab hcross⟩
    unfold firstUpperPassage
    simp only [if_pos ha, if_pos hb]
    exact_mod_cast (csInf_le_csInf' hb
      (show {t : ℝ≥0 | 0 < t ∧ b < X t ω} ⊆
        {t : ℝ≥0 | 0 < t ∧ a < X t ω} by
          intro t ht
          exact ⟨ht.1, lt_of_le_of_lt hab ht.2⟩))
  · unfold firstUpperPassage
    simp only [if_neg hb, le_top]
