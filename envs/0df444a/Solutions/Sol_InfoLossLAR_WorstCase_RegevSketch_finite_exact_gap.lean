-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.finite_exact_gap
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T12:19:50.147788+00:00
-- url     : https://prove2.me/submissions/bca4d96f-fc4d-4155-9d6b-fd8fd45b9c88

import Definitions.Def_InfoLossLAR_WorstCase_Family
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_exact_gap_binary_decider
import Theorems.Thm_InfoLossLAR_WorstCase_poly_program_first_bit_qpt

set_option autoImplicit false

open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.RegevSketch

theorem solution (cutoff : ℕ) :
    ∃ E : Family, IsQPT E ∧ ∀ n : ℕ, 1 ≤ n → n < cutoff → SolvesGapSVP E (famN n) 1 := by
  obtain ⟨f, P, h_decides⟩ := finite_exact_gap_binary_decider cutoff
  obtain ⟨E, h_qpt, h_accept⟩ := poly_program_first_bit_qpt f P
  refine ⟨E, h_qpt, ?_⟩
  change ∀ n : ℕ, 1 ≤ n → n < cutoff → SolvesGapSVP E n 1
  intro n h_pos h_cutoff B h_det δ h_threshold
  have h_iff := h_decides n h_pos h_cutoff B h_det δ h_threshold
  rw [h_accept]
  constructor
  · intro h_short
    rw [if_pos (h_iff.mpr h_short)]
    norm_num
  · intro h_long
    have h_false : ¬ (f (encGapInstance B δ))[0]? = some true :=
      fun h => (not_le_of_gt (by simpa only [one_mul] using h_long)) (h_iff.mp h)
    rw [if_neg h_false]
    norm_num
