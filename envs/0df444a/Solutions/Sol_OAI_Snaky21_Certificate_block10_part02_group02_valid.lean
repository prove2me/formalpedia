-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part02_group02_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:34:03.338098+00:00
-- url     : https://prove2.me/submissions/c5d72889-bb73-4ec9-a956-a4b3551edfa3

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part02_group01_valid
import Definitions.Def_Snaky21Data10
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_valid
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
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_17 : Valid card_17 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_32 : Valid card_32 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_50 : Valid card_50 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_59 : Valid card_59 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_79 : Valid card_79 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_90 : Valid card_90 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_105 : Valid card_105 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_128 : Valid card_128 := block02_valid.1
theorem valid_150 : Valid card_150 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_179 : Valid card_179 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_222 : Valid card_222 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_243 : Valid card_243 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_377 : Valid card_377 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_386 : Valid card_386 := block06_valid.2.2.1
theorem valid_408 : Valid card_408 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_410 : Valid card_410 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_422 : Valid card_422 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_426 : Valid card_426 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_430 : Valid card_430 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_431 : Valid card_431 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_450 : Valid card_450 := block07_valid.2.2.1
theorem valid_475 : Valid card_475 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_503 : Valid card_503 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_509 : Valid card_509 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_510 : Valid card_510 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_587 : Valid card_587 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_592 : Valid card_592 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_604 : Valid card_604 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_642 : Valid card_642 := block10_part00_valid.2.2.1
theorem valid_646 : Valid card_646 := block10_part00_valid.2.2.2.2.2.2.1

theorem valid_676 : Valid card_676 := block10_part02_group01_valid.1
theorem valid_678 : Valid card_678 := block10_part02_group01_valid.2.2.1
theorem valid_679 : Valid card_679 := block10_part02_group01_valid.2.2.2.1

theorem eq_inline_691 : inline_691 = combine (1, 3) [placed 4 (4, 0) card_56, placed 6 (5, 5) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_691 : Valid inline_691 := by
  rw [eq_inline_691]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_56
  subst c
  exact placed_valid 6 (5, 5) valid_179

theorem eq_card_680 : card_680 = combine (3, 3) [placed 6 (5, 3) card_0, inline_691] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_680 : Valid card_680 := by
  rw [eq_card_680]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 3) valid_0
  subst c
  exact valid_inline_691

theorem eq_inline_692 : inline_692 = combine (4, 3) [placed 7 (5, 6) card_32, placed 5 (1, 4) card_44, placed 5 (3, 6) card_90] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_692 : Valid inline_692 := by
  rw [eq_inline_692]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_32
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_44
  subst c
  exact placed_valid 5 (3, 6) valid_90

theorem eq_inline_693 : inline_693 = combine (4, 3) [placed 0 (3, 3) card_17, placed 7 (5, 6) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_693 : Valid inline_693 := by
  rw [eq_inline_693]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_17
  subst c
  exact placed_valid 7 (5, 6) valid_32

theorem eq_inline_694 : inline_694 = combine (4, 6) [placed 6 (4, 7) card_44, placed 6 (4, 7) card_52, inline_692, inline_693] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_694 : Valid inline_694 := by
  rw [eq_inline_694]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_52
  rcases hc with rfl | hc
  · exact valid_inline_692
  subst c
  exact valid_inline_693

theorem eq_card_681 : card_681 = combine (3, 4) [placed 1 (0, 4) card_11, inline_694] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_681 : Valid card_681 := by
  rw [eq_card_681]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_11
  subst c
  exact valid_inline_694

theorem eq_inline_695 : inline_695 = combine (4, 3) [placed 4 (4, 2) card_44, placed 4 (4, 2) card_52, placed 2 (3, 7) card_128, placed 1 (1, 2) card_676] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_695 : Valid inline_695 := by
  rw [eq_inline_695]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_128
  subst c
  exact placed_valid 1 (1, 2) valid_676

theorem eq_inline_696 : inline_696 = combine (6, 7) [placed 0 (6, 3) card_7, placed 4 (7, 3) card_9, placed 3 (8, 4) card_386] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_696 : Valid inline_696 := by
  rw [eq_inline_696]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_9
  subst c
  exact placed_valid 3 (8, 4) valid_386

theorem eq_inline_697 : inline_697 = combine (5, 6) [placed 6 (7, 6) card_0, placed 1 (2, 4) card_222] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_697 : Valid inline_697 := by
  rw [eq_inline_697]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_0
  subst c
  exact placed_valid 1 (2, 4) valid_222

theorem eq_inline_698 : inline_698 = combine (4, 6) [placed 4 (7, 3) card_377, inline_696, placed 0 (2, 3) card_426, inline_697] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_698 : Valid inline_698 := by
  rw [eq_inline_698]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_377
  rcases hc with rfl | hc
  · exact valid_inline_696
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_426
  subst c
  exact valid_inline_697

theorem eq_inline_699 : inline_699 = combine (6, 6) [placed 4 (7, 2) card_13, placed 6 (7, 8) card_14, placed 2 (3, 7) card_79, placed 4 (7, 3) card_679, inline_698] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_699 : Valid inline_699 := by
  rw [eq_inline_699]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_679
  subst c
  exact valid_inline_698

theorem eq_inline_700 : inline_700 = combine (6, 5) [placed 2 (3, 8) card_59, placed 5 (2, 5) card_105, placed 4 (7, 1) card_678, inline_699] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_700 : Valid inline_700 := by
  rw [eq_inline_700]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_105
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 1) valid_678
  subst c
  exact valid_inline_699

theorem eq_inline_701 : inline_701 = combine (6, 6) [placed 6 (7, 8) card_13, placed 2 (3, 7) card_79, placed 4 (7, 2) card_243, placed 4 (7, 3) card_679] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_701 : Valid inline_701 := by
  rw [eq_inline_701]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_243
  subst c
  exact placed_valid 4 (7, 3) valid_679

theorem eq_inline_702 : inline_702 = combine (6, 5) [placed 0 (3, 1) card_430, placed 0 (2, 2) card_431, placed 7 (7, 5) card_592, placed 4 (7, 1) card_678, inline_701, placed 2 (2, 9) card_681] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_702 : Valid inline_702 := by
  rw [eq_inline_702]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_430
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_431
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_592
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 1) valid_678
  rcases hc with rfl | hc
  · exact valid_inline_701
  subst c
  exact placed_valid 2 (2, 9) valid_681

theorem eq_inline_703 : inline_703 = combine (6, 4) [placed 4 (7, 2) card_422, placed 2 (2, 8) card_450, placed 6 (7, 7) card_503, placed 0 (3, 0) card_642, inline_700, placed 2 (2, 7) card_680, inline_702] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_703 : Valid inline_703 := by
  rw [eq_inline_703]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_422
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_450
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 7) valid_503
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_642
  rcases hc with rfl | hc
  · exact valid_inline_700
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_680
  subst c
  exact valid_inline_702

theorem eq_card_682 : card_682 = combine (4, 4) [placed 2 (3, 8) card_408, placed 2 (3, 8) card_410, placed 6 (6, 8) card_475, placed 5 (1, 7) card_509, placed 7 (7, 7) card_510, placed 2 (2, 8) card_587, placed 6 (7, 8) card_646, inline_695, inline_703] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_682 : Valid card_682 := by
  rw [eq_card_682]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_408
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_410
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_509
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 7) valid_510
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_646
  rcases hc with rfl | hc
  · exact valid_inline_695
  subst c
  exact valid_inline_703

theorem eq_inline_704 : inline_704 = combine (2, 5) [placed 6 (4, 5) card_5, placed 5 (0, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_704 : Valid inline_704 := by
  rw [eq_inline_704]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_5
  subst c
  exact placed_valid 5 (0, 6) valid_9

theorem eq_inline_705 : inline_705 = combine (2, 5) [placed 6 (4, 5) card_5, placed 0 (1, 2) card_604] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_705 : Valid inline_705 := by
  rw [eq_inline_705]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_5
  subst c
  exact placed_valid 0 (1, 2) valid_604

theorem eq_card_683 : card_683 = combine (3, 5) [placed 1 (0, 4) card_50, placed 1 (0, 4) card_150, inline_704, inline_705, placed 2 (0, 10) card_682] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_683 : Valid card_683 := by
  rw [eq_card_683]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_150
  rcases hc with rfl | hc
  · exact valid_inline_704
  rcases hc with rfl | hc
  · exact valid_inline_705
  subst c
  exact placed_valid 2 (0, 10) valid_682


end OAI.Snaky21.Certificate

theorem solution : Valid card_680 ∧ Valid card_681 ∧ Valid card_682 ∧ Valid card_683 ∧ True :=
  ⟨valid_680, valid_681, valid_682, valid_683, True.intro⟩
