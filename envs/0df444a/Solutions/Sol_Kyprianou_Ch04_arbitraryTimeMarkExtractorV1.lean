-- Prove2me | solution 1 for Kyprianou.Ch04.arbitraryTimeMarkExtractorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:14:39.80282+00:00
-- url     : https://prove2.me/submissions/5efe3edb-80ce-4d93-b6da-dc592d2a0478

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
import Theorems.Thm_Kyprianou_Ch04_arbitraryTimeMarkCandidateSeriesMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_arbitraryTimeMarkCandidateSeriesCardV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- Extract the count in an arbitrary Borel time-mark set from a real cadlag path. -/
theorem solution (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) :
    ∃ G : (NNReal → ℝ) → ENNReal, Measurable G ∧
      ∀ Y : NNReal → ℝ,
      (∀ u, ContinuousWithinAt Y (Ici u) u) →
      (∀ u, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      ({u : NNReal | 0 < u ∧ Y u - Function.leftLim Y u ≠ 0 ∧
        ((u : ℝ), Y u - Function.leftLim Y u) ∈ D}).encard = G Y := by
  obtain ⟨time, mark, ht, hm, hExact⟩ :=
    AvramDividend.Classical.avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
  refine ⟨_, Kyprianou.Ch04.arbitraryTimeMarkCandidateSeriesMeasurableV1 time mark ht hm D hD, ?_⟩
  intro Y hR hL
  obtain ⟨hMark, hCover⟩ := hExact Y hR hL
  exact Kyprianou.Ch04.arbitraryTimeMarkCandidateSeriesCardV1 Y
    (fun k => time k Y) (fun k => mark k Y) hMark hCover D
