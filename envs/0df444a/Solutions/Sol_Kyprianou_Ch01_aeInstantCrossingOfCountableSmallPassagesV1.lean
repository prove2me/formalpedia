-- Prove2me | solution 1 for Kyprianou.Ch01.aeInstantCrossingOfCountableSmallPassagesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:11:20.995727+00:00
-- url     : https://prove2.me/submissions/71326036-0762-4876-9a49-b1b3e3bd2e57

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_crossingBefore_of_ltV1
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (δ : ℕ → ℝ≥0)
    (hδ : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, δ n < ε)
    (hSmall : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∃ s : ℝ≥0, 0 < s ∧
        firstUpperPassage X (s : ℝ) ω < (δ n : WithTop ℝ≥0)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < X t ω := by
  have hAll :
      ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ s : ℝ≥0, 0 < s ∧
        firstUpperPassage X (s : ℝ) ω < (δ n : WithTop ℝ≥0) :=
    ae_all_iff.mpr hSmall
  filter_upwards [hAll] with ω hw
  intro ε hε
  obtain ⟨n, hn⟩ := hδ ε hε
  obtain ⟨s, hs, ht⟩ := hw n
  obtain ⟨t, htPos, htSmall, hCross⟩ :=
    firstUpperPassage_crossingBefore_of_ltV1
      X (s : ℝ) ω (δ n) ht
  have hsPos : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast hs
  exact ⟨t, htPos, lt_trans htSmall hn, lt_trans hsPos hCross⟩
