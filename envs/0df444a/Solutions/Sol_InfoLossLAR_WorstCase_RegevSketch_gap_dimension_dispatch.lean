-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.gap_dimension_dispatch
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:02:10.794963+00:00
-- url     : https://prove2.me/submissions/a6de7967-6ca4-4100-808e-6c5382c78456
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_qpt_bool_dispatch
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_gap_dimension_classifier

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.RegevSketch

theorem solution (E A : Family) (hE : IsQPT E) (hA : IsQPT A)
    (cutoff : ℕ) :
  ∃ P : Family, IsQPT P ∧ ∀ n : ℕ, ∀ B : Matrix (Fin (famN n)) (Fin (famN n)) ℤ,
    ∀ δ : ℚ, acceptProb P (encGapInstance B δ) =
      if n < cutoff then acceptProb E (encGapInstance B δ) else acceptProb A (encGapInstance B δ) := by
  obtain ⟨f, hf, hparse⟩ := gap_dimension_classifier cutoff
  obtain ⟨P, hP, hprob⟩ := qpt_bool_dispatch E A hE hA f hf
  refine ⟨P, hP, ?_⟩
  intro n B δ
  have h := hprob (encGapInstance B δ)
  rw [hparse n B δ] at h
  simpa using h
