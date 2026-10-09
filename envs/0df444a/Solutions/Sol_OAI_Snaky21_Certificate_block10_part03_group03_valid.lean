-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part03_group03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:49:45.254777+00:00
-- url     : https://prove2.me/submissions/e340d295-d3df-47fb-84a3-422a14f8de44

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part03_group02_valid
import Definitions.Def_Snaky21Data10
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part02_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
namespace OAI.Snaky21
theorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i
theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h
end OAI.Snaky21

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OAI.Snaky21.Certificate
theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl
theorem valid_0 : Valid card_0 := block00_valid.1
theorem valid_3 : Valid card_3 := block00_valid.2.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_18 : Valid card_18 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_27 : Valid card_27 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_30 : Valid card_30 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_39 : Valid card_39 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_40 : Valid card_40 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_49 : Valid card_49 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_61 : Valid card_61 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_77 : Valid card_77 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_101 : Valid card_101 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_103 : Valid card_103 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_108 : Valid card_108 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_157 : Valid card_157 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_186 : Valid card_186 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_195 : Valid card_195 := block03_valid.2.2.2.1
theorem valid_197 : Valid card_197 := block03_valid.2.2.2.2.2.1
theorem valid_204 : Valid card_204 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_304 : Valid card_304 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_322 : Valid card_322 := block05_valid.2.2.1
theorem valid_325 : Valid card_325 := block05_valid.2.2.2.2.2.1
theorem valid_348 : Valid card_348 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_369 : Valid card_369 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_372 : Valid card_372 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_400 : Valid card_400 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_460 : Valid card_460 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_463 : Valid card_463 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_511 : Valid card_511 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_516 : Valid card_516 := block08_valid.2.2.2.2.1
theorem valid_683 : Valid card_683 := block10_part02_valid.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_697 : Valid card_697 := block10_part03_group02_valid.2.1
theorem valid_699 : Valid card_699 := block10_part03_group02_valid.2.2.2.1

theorem eq_inline_767 : inline_767 = combine (2, 5) [placed 1 (0, 4) card_39, placed 0 (1, 2) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_767 : Valid inline_767 := by
  rw [eq_inline_767]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_39
  subst c
  exact placed_valid 0 (1, 2) valid_52

theorem eq_inline_768 : inline_768 = combine (3, 5) [placed 6 (4, 5) card_5, placed 2 (1, 6) card_197] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_768 : Valid inline_768 := by
  rw [eq_inline_768]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_5
  subst c
  exact placed_valid 2 (1, 6) valid_197

theorem eq_inline_769 : inline_769 = combine (2, 5) [placed 1 (1, 2) card_0, inline_768] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_769 : Valid inline_769 := by
  rw [eq_inline_769]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_0
  subst c
  exact valid_inline_768

theorem eq_inline_770 : inline_770 = combine (2, 6) [placed 0 (1, 2) card_61, placed 1 (0, 3) card_348, inline_769] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_770 : Valid inline_770 := by
  rw [eq_inline_770]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_61
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_348
  subst c
  exact valid_inline_769

theorem eq_inline_771 : inline_771 = combine (4, 4) [placed 4 (4, 2) card_7, placed 5 (3, 6) card_8, placed 2 (3, 7) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_771 : Valid inline_771 := by
  rw [eq_inline_771]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_8
  subst c
  exact placed_valid 2 (3, 7) valid_9

theorem eq_inline_772 : inline_772 = combine (2, 5) [placed 1 (0, 4) card_40, placed 0 (1, 2) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_772 : Valid inline_772 := by
  rw [eq_inline_772]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_40
  subst c
  exact placed_valid 0 (1, 2) valid_52

theorem eq_inline_773 : inline_773 = combine (4, 6) [placed 6 (5, 8) card_304, inline_771, inline_772] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_773 : Valid inline_773 := by
  rw [eq_inline_773]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_304
  rcases hc with rfl | hc
  · exact valid_inline_771
  subst c
  exact valid_inline_772

theorem eq_card_700 : card_700 = combine (4, 5) [placed 2 (0, 8) card_204, inline_767, placed 0 (3, 0) card_460, inline_770, inline_773] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_700 : Valid card_700 := by
  rw [eq_card_700]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_204
  rcases hc with rfl | hc
  · exact valid_inline_767
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_460
  rcases hc with rfl | hc
  · exact valid_inline_770
  subst c
  exact valid_inline_773

theorem eq_inline_774 : inline_774 = combine (5, 8) [placed 5 (4, 8) card_10, placed 4 (6, 6) card_39] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_774 : Valid inline_774 := by
  rw [eq_inline_774]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_10
  subst c
  exact placed_valid 4 (6, 6) valid_39

theorem eq_inline_775 : inline_775 = combine (5, 8) [placed 3 (8, 7) card_52, placed 1 (1, 6) card_325] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_775 : Valid inline_775 := by
  rw [eq_inline_775]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 7) valid_52
  subst c
  exact placed_valid 1 (1, 6) valid_325

theorem eq_inline_776 : inline_776 = combine (4, 7) [placed 4 (7, 6) card_8, placed 1 (2, 6) card_463] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_776 : Valid inline_776 := by
  rw [eq_inline_776]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 6) valid_8
  subst c
  exact placed_valid 1 (2, 6) valid_463

theorem eq_inline_777 : inline_777 = combine (4, 8) [placed 5 (4, 8) card_18, placed 4 (7, 6) card_348] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_777 : Valid inline_777 := by
  rw [eq_inline_777]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_18
  subst c
  exact placed_valid 4 (7, 6) valid_348

theorem eq_inline_778 : inline_778 = combine (5, 9) [placed 5 (5, 10) card_5, placed 0 (4, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_778 : Valid inline_778 := by
  rw [eq_inline_778]
  apply combination_rule (5, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 10) valid_5
  subst c
  exact placed_valid 0 (4, 6) valid_9

theorem eq_inline_779 : inline_779 = combine (5, 9) [placed 5 (5, 10) card_5, placed 0 (4, 6) card_372] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_779 : Valid inline_779 := by
  rw [eq_inline_779]
  apply combination_rule (5, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 10) valid_5
  subst c
  exact placed_valid 0 (4, 6) valid_372

theorem eq_inline_780 : inline_780 = combine (5, 8) [placed 5 (4, 8) card_10, inline_778, inline_779] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_780 : Valid inline_780 := by
  rw [eq_inline_780]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_10
  rcases hc with rfl | hc
  · exact valid_inline_778
  subst c
  exact valid_inline_779

theorem eq_inline_781 : inline_781 = combine (5, 10) [inline_774, placed 3 (10, 6) card_683, inline_775, inline_776, inline_777, placed 1 (2, 6) card_700, inline_780] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_781 : Valid inline_781 := by
  rw [eq_inline_781]
  apply combination_rule (5, 10) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_774
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 6) valid_683
  rcases hc with rfl | hc
  · exact valid_inline_775
  rcases hc with rfl | hc
  · exact valid_inline_776
  rcases hc with rfl | hc
  · exact valid_inline_777
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 6) valid_700
  subst c
  exact valid_inline_780

theorem eq_card_701 : card_701 = combine (7, 7) [placed 5 (3, 8) card_12, placed 4 (8, 3) card_322, placed 0 (4, 4) card_435, placed 6 (9, 10) card_697, placed 0 (1, 2) card_699, inline_781] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_701 : Valid card_701 := by
  rw [eq_card_701]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 10) valid_697
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_699
  subst c
  exact valid_inline_781

theorem eq_inline_782 : inline_782 = combine (1, 1) [placed 0 (1, 0) card_15, placed 1 (0, 1) card_40] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_782 : Valid inline_782 := by
  rw [eq_inline_782]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_15
  subst c
  exact placed_valid 1 (0, 1) valid_40

theorem eq_inline_783 : inline_783 = combine (4, 2) [placed 1 (1, 2) card_30, placed 0 (0, 0) card_108, inline_782, placed 0 (1, 0) card_511] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_783 : Valid inline_783 := by
  rw [eq_inline_783]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_108
  rcases hc with rfl | hc
  · exact valid_inline_782
  subst c
  exact placed_valid 0 (1, 0) valid_511

theorem eq_card_702 : card_702 = combine (4, 3) [placed 5 (0, 3) card_22, placed 0 (0, 1) card_400, inline_783] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_702 : Valid card_702 := by
  rw [eq_card_702]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_400
  subst c
  exact valid_inline_783

theorem eq_inline_784 : inline_784 = combine (5, 3) [placed 4 (5, 3) card_3, placed 0 (4, 2) card_27] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_784 : Valid inline_784 := by
  rw [eq_inline_784]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_3
  subst c
  exact placed_valid 0 (4, 2) valid_27

theorem eq_inline_785 : inline_785 = combine (2, 3) [placed 4 (5, 3) card_0, placed 2 (2, 6) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_785 : Valid inline_785 := by
  rw [eq_inline_785]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_0
  subst c
  exact placed_valid 2 (2, 6) valid_52

theorem eq_inline_786 : inline_786 = combine (3, 2) [placed 7 (4, 6) card_0, placed 2 (2, 6) card_101] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_786 : Valid inline_786 := by
  rw [eq_inline_786]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 6) valid_0
  subst c
  exact placed_valid 2 (2, 6) valid_101

theorem eq_inline_787 : inline_787 = combine (3, 3) [placed 0 (3, 2) card_195, inline_784, inline_785, inline_786] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_787 : Valid inline_787 := by
  rw [eq_inline_787]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_195
  rcases hc with rfl | hc
  · exact valid_inline_784
  rcases hc with rfl | hc
  · exact valid_inline_785
  subst c
  exact valid_inline_786

theorem eq_inline_788 : inline_788 = combine (2, 2) [placed 3 (6, 2) card_11, placed 1 (2, 2) card_103, placed 4 (5, 1) card_157] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_788 : Valid inline_788 := by
  rw [eq_inline_788]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_103
  subst c
  exact placed_valid 4 (5, 1) valid_157

theorem eq_inline_789 : inline_789 = combine (5, 2) [placed 5 (4, 5) card_5, inline_788] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_789 : Valid inline_789 := by
  rw [eq_inline_789]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 5) valid_5
  subst c
  exact valid_inline_788

theorem eq_inline_790 : inline_790 = combine (3, 2) [placed 7 (4, 5) card_5, inline_789] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_790 : Valid inline_790 := by
  rw [eq_inline_790]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_5
  subst c
  exact valid_inline_789

theorem eq_inline_791 : inline_791 = combine (4, 2) [placed 2 (4, 6) card_7, placed 6 (5, 6) card_9, inline_790] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_791 : Valid inline_791 := by
  rw [eq_inline_791]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_9
  subst c
  exact valid_inline_790

theorem eq_inline_792 : inline_792 = combine (5, 3) [placed 4 (5, 3) card_18, placed 4 (5, 2) card_77] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_792 : Valid inline_792 := by
  rw [eq_inline_792]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_18
  subst c
  exact placed_valid 4 (5, 2) valid_77

theorem eq_inline_793 : inline_793 = combine (4, 6) [placed 6 (5, 7) card_9, placed 3 (5, 3) card_49, placed 0 (3, 1) card_186, inline_792] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_793 : Valid inline_793 := by
  rw [eq_inline_793]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_49
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_186
  subst c
  exact valid_inline_792

theorem eq_card_703 : card_703 = combine (4, 3) [placed 6 (5, 7) card_13, placed 4 (5, 0) card_369, inline_787, placed 2 (1, 6) card_516, inline_791, inline_793] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_703 : Valid card_703 := by
  rw [eq_card_703]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 0) valid_369
  rcases hc with rfl | hc
  · exact valid_inline_787
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_516
  rcases hc with rfl | hc
  · exact valid_inline_791
  subst c
  exact valid_inline_793


end OAI.Snaky21.Certificate

theorem solution : Valid card_700 ∧ Valid card_701 ∧ Valid card_702 ∧ Valid card_703 ∧ True :=
  ⟨valid_700, valid_701, valid_702, valid_703, True.intro⟩
