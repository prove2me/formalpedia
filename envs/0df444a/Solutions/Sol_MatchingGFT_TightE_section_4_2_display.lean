-- Prove2me | solution 1 for MatchingGFT.TightE.section_4_2_display
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:41:36.752303+00:00
-- url     : https://prove2.me/submissions/1272823d-4085-4b66-8644-a094cb529ae1

import Mathlib
import Definitions.Def_MatchingGFT_TightE_CappedExp
import Theorems.Thm_MatchingGFT_TightE_lemma_4_2

open MatchingGFT.TightE in
theorem solution (L : ℝ) (hL : 2 ≤ L) :
    cappedPS L = cappedPB L ∧ cappedPB L < cappedD L ∧ cappedD L < cappedG L := by
  obtain ⟨-, -, -, -, -, -, -, hg, hps, hpb⟩ := lemma_4_2 L hL
  have hL0 : 0 < L := by linarith
  have hE2 : 2 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hA : 0 < Real.exp (-L) := Real.exp_pos _
  have hw0 : 0 ≤ (L - 2) / Real.exp 1 := div_nonneg (by linarith) hE0.le
  have hw : (L - 2) / Real.exp 1 ≤ (L - 2) / 2 :=
    div_le_div_of_nonneg_left (by linarith) two_pos hE2.le
  have hu0 : 0 < 1 / L := by positivity
  have hu : 1 / L ≤ 1 / 2 := one_div_le_one_div_of_le two_pos hL
  have hP : 0 < Real.exp (-L) * (1 + (L - 2) / Real.exp 1) := mul_pos hA (by linarith)
  refine ⟨by rw [hps, hpb], ?_, ?_⟩
  · unfold cappedD
    rw [hps, hpb]
    nlinarith [mul_pos hu0 hP]
  · unfold cappedD
    rw [hps, hg]
    have key : (1 + 1 / L) * (1 + (L - 2) / Real.exp 1) < L := by
      nlinarith [mul_le_mul hu hw hw0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc (1 + 1 / L) * (Real.exp (-L) * (1 + (L - 2) / Real.exp 1))
        = Real.exp (-L) * ((1 + 1 / L) * (1 + (L - 2) / Real.exp 1)) := by ring
      _ < Real.exp (-L) * L := mul_lt_mul_of_pos_left key hA
      _ = L * Real.exp (-L) := by ring
