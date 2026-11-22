-- Prove2me | solution 1 for Kyprianou.Ch01.firstLowerPassage_spatialTranslationForMcKean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:15:08.426064+00:00
-- url     : https://prove2.me/submissions/49850731-491d-43c7-98ec-dfd549a0299a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (x barrier : ℝ) :
    firstLowerPassage X x barrier =
      firstLowerPassage X 0 (barrier - x) := by
  classical
  funext ω
  have hiff (t : ℝ≥0) :
      (0 < t ∧ x + X t ω < barrier) ↔
        (0 < t ∧ 0 + X t ω < barrier - x) := by
    constructor
    · rintro ⟨ht, hc⟩
      exact ⟨ht, by linarith⟩
    · rintro ⟨ht, hc⟩
      exact ⟨ht, by linarith⟩
  have hex :
      (∃ t : ℝ≥0, 0 < t ∧ x + X t ω < barrier) ↔
        (∃ t : ℝ≥0, 0 < t ∧ 0 + X t ω < barrier - x) :=
    exists_congr hiff
  have hset :
      {t : ℝ≥0 | 0 < t ∧ x + X t ω < barrier} =
        {t : ℝ≥0 | 0 < t ∧ 0 + X t ω < barrier - x} :=
    Set.ext (fun t => hiff t)
  unfold firstLowerPassage
  simp only [hex, hset]
