-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part01_group03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:22:05.346278+00:00
-- url     : https://prove2.me/submissions/ef93ddf7-82e4-4f41-acbc-ad17f6441f72

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_group01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_group02_valid
import Definitions.Def_Snaky21Data10
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_valid
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
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_19 : Valid card_19 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_24 : Valid card_24 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_25 : Valid card_25 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_28 : Valid card_28 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_31 : Valid card_31 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_36 : Valid card_36 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_40 : Valid card_40 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_48 : Valid card_48 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_66 : Valid card_66 := block01_valid.2.2.1
theorem valid_98 : Valid card_98 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_106 : Valid card_106 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_125 : Valid card_125 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_126 : Valid card_126 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_136 : Valid card_136 := block02_valid.2.2.2.2.2.2.2.2.1
theorem valid_188 : Valid card_188 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_197 : Valid card_197 := block03_valid.2.2.2.2.2.1
theorem valid_219 : Valid card_219 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_225 : Valid card_225 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_270 : Valid card_270 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_355 : Valid card_355 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_356 : Valid card_356 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_434 : Valid card_434 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_441 : Valid card_441 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_442 : Valid card_442 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_459 : Valid card_459 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_464 : Valid card_464 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_512 : Valid card_512 := block08_valid.1
theorem valid_514 : Valid card_514 := block08_valid.2.2.1
theorem valid_530 : Valid card_530 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_535 : Valid card_535 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_588 : Valid card_588 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_590 : Valid card_590 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_617 : Valid card_617 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_638 : Valid card_638 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_660 : Valid card_660 := block10_part01_group01_valid.1
theorem valid_661 : Valid card_661 := block10_part01_group01_valid.2.1
theorem valid_663 : Valid card_663 := block10_part01_group01_valid.2.2.2.1
theorem valid_665 : Valid card_665 := block10_part01_group02_valid.2.1
theorem valid_666 : Valid card_666 := block10_part01_group02_valid.2.2.1
theorem valid_667 : Valid card_667 := block10_part01_group02_valid.2.2.2.1

theorem eq_card_668 : card_668 = combine (3, 4) [placed 4 (3, 0) card_7, placed 0 (2, 0) card_9, placed 0 (0, 1) card_666] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_668 : Valid card_668 := by
  rw [eq_card_668]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_9
  subst c
  exact placed_valid 0 (0, 1) valid_666

theorem eq_inline_644 : inline_644 = combine (5, 6) [placed 6 (7, 6) card_0, placed 7 (7, 7) card_66] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_644 : Valid inline_644 := by
  rw [eq_inline_644]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_0
  subst c
  exact placed_valid 7 (7, 7) valid_66

theorem eq_inline_645 : inline_645 = combine (4, 6) [placed 7 (4, 8) card_0, inline_644] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_645 : Valid inline_645 := by
  rw [eq_inline_645]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 8) valid_0
  subst c
  exact valid_inline_644

theorem eq_inline_646 : inline_646 = combine (3, 7) [placed 2 (3, 7) card_5, placed 0 (3, 4) card_36] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_646 : Valid inline_646 := by
  rw [eq_inline_646]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_5
  subst c
  exact placed_valid 0 (3, 4) valid_36

theorem eq_inline_647 : inline_647 = combine (3, 7) [placed 4 (6, 6) card_24, placed 0 (3, 4) card_36] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_647 : Valid inline_647 := by
  rw [eq_inline_647]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 6) valid_24
  subst c
  exact placed_valid 0 (3, 4) valid_36

theorem eq_inline_648 : inline_648 = combine (4, 7) [placed 3 (7, 6) card_48, inline_645, inline_646, inline_647] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_648 : Valid inline_648 := by
  rw [eq_inline_648]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 6) valid_48
  rcases hc with rfl | hc
  · exact valid_inline_645
  rcases hc with rfl | hc
  · exact valid_inline_646
  subst c
  exact valid_inline_647

theorem eq_inline_649 : inline_649 = combine (5, 7) [placed 3 (6, 4) card_5, inline_648] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_649 : Valid inline_649 := by
  rw [eq_inline_649]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_5
  subst c
  exact valid_inline_648

theorem eq_inline_650 : inline_650 = combine (4, 5) [placed 7 (7, 7) card_25, inline_649] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_650 : Valid inline_650 := by
  rw [eq_inline_650]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 7) valid_25
  subst c
  exact valid_inline_649

theorem eq_inline_651 : inline_651 = combine (6, 7) [placed 4 (7, 3) card_19, placed 1 (5, 4) card_197, placed 4 (7, 3) card_225, inline_650] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_651 : Valid inline_651 := by
  rw [eq_inline_651]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 4) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_225
  subst c
  exact valid_inline_650

theorem eq_card_669 : card_669 = combine (6, 4) [placed 2 (4, 8) card_188, placed 4 (7, 3) card_590, placed 2 (3, 7) card_668, inline_651] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_669 : Valid card_669 := by
  rw [eq_card_669]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_590
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_668
  subst c
  exact valid_inline_651

theorem eq_inline_652 : inline_652 = combine (5, 5) [placed 7 (7, 6) card_40, placed 1 (2, 4) card_125, placed 1 (1, 1) card_660] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_652 : Valid inline_652 := by
  rw [eq_inline_652]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 1 (1, 1) valid_660

theorem eq_inline_653 : inline_653 = combine (5, 5) [placed 7 (7, 6) card_40, placed 1 (2, 4) card_125, placed 1 (1, 3) card_663] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_653 : Valid inline_653 := by
  rw [eq_inline_653]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 1 (1, 3) valid_663

theorem eq_inline_654 : inline_654 = combine (7, 6) [placed 1 (3, 5) card_106, placed 1 (3, 5) card_219, placed 2 (5, 9) card_530] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_654 : Valid inline_654 := by
  rw [eq_inline_654]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 5) valid_106
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 5) valid_219
  subst c
  exact placed_valid 2 (5, 9) valid_530

theorem eq_inline_655 : inline_655 = combine (5, 5) [placed 7 (7, 6) card_40, placed 5 (2, 5) card_98, placed 2 (4, 9) card_512] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_655 : Valid inline_655 := by
  rw [eq_inline_655]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_98
  subst c
  exact placed_valid 2 (4, 9) valid_512

theorem eq_inline_656 : inline_656 = combine (5, 6) [placed 0 (3, 4) card_270, placed 4 (7, 3) card_588, placed 2 (4, 9) card_638, inline_654, inline_655] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_656 : Valid inline_656 := by
  rw [eq_inline_656]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_270
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_588
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 9) valid_638
  rcases hc with rfl | hc
  · exact valid_inline_654
  subst c
  exact valid_inline_655

theorem eq_inline_657 : inline_657 = combine (5, 5) [placed 7 (7, 6) card_40, placed 1 (2, 4) card_125, placed 0 (2, 1) card_617] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_657 : Valid inline_657 := by
  rw [eq_inline_657]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 0 (2, 1) valid_617

theorem eq_inline_658 : inline_658 = combine (6, 4) [placed 2 (5, 8) card_13, placed 2 (5, 8) card_31, placed 2 (3, 7) card_355, placed 2 (3, 8) card_356, placed 0 (2, 3) card_434, placed 1 (3, 3) card_435, placed 6 (7, 8) card_441] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_658 : Valid inline_658 := by
  rw [eq_inline_658]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_355
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_356
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_435
  subst c
  exact placed_valid 6 (7, 8) valid_441

theorem eq_inline_659 : inline_659 = combine (5, 5) [placed 7 (7, 6) card_40, placed 1 (2, 4) card_125, placed 2 (4, 10) card_535] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_659 : Valid inline_659 := by
  rw [eq_inline_659]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 2 (4, 10) valid_535

theorem eq_inline_660 : inline_660 = combine (6, 4) [placed 0 (4, 2) card_188, placed 2 (4, 8) card_188, placed 6 (7, 8) card_441, placed 6 (7, 8) card_442, placed 4 (7, 3) card_514, placed 2 (3, 7) card_667] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_660 : Valid inline_660 := by
  rw [eq_inline_660]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_441
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_442
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_514
  subst c
  exact placed_valid 2 (3, 7) valid_667

theorem eq_inline_661 : inline_661 = combine (5, 5) [placed 1 (2, 4) card_125, placed 2 (4, 7) card_136] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_661 : Valid inline_661 := by
  rw [eq_inline_661]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 2 (4, 7) valid_136

theorem eq_inline_662 : inline_662 = combine (6, 4) [placed 4 (7, 2) card_13, placed 4 (7, 3) card_514, placed 4 (7, 3) card_590, placed 2 (3, 7) card_668, inline_661] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_662 : Valid inline_662 := by
  rw [eq_inline_662]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_514
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_590
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_668
  subst c
  exact valid_inline_661

theorem eq_card_670 : card_670 = combine (6, 6) [placed 0 (5, 1) card_459, inline_652, placed 2 (2, 10) card_661, inline_653, inline_656, inline_657, inline_658, inline_659, placed 1 (0, 2) card_665, inline_660, inline_662, placed 0 (0, 0) card_669] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_670 : Valid card_670 := by
  rw [eq_card_670]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 1) valid_459
  rcases hc with rfl | hc
  · exact valid_inline_652
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_661
  rcases hc with rfl | hc
  · exact valid_inline_653
  rcases hc with rfl | hc
  · exact valid_inline_656
  rcases hc with rfl | hc
  · exact valid_inline_657
  rcases hc with rfl | hc
  · exact valid_inline_658
  rcases hc with rfl | hc
  · exact valid_inline_659
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_665
  rcases hc with rfl | hc
  · exact valid_inline_660
  rcases hc with rfl | hc
  · exact valid_inline_662
  subst c
  exact placed_valid 0 (0, 0) valid_669

theorem eq_inline_663 : inline_663 = combine (3, 4) [placed 7 (5, 4) card_22, placed 4 (4, 0) card_464] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_663 : Valid inline_663 := by
  rw [eq_inline_663]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_22
  subst c
  exact placed_valid 4 (4, 0) valid_464

theorem eq_card_671 : card_671 = combine (3, 3) [placed 1 (0, 2) card_28, placed 1 (0, 2) card_126, placed 5 (0, 4) card_126, inline_663] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_671 : Valid card_671 := by
  rw [eq_card_671]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_126
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_126
  subst c
  exact valid_inline_663


end OAI.Snaky21.Certificate

theorem solution : Valid card_668 ∧ Valid card_669 ∧ Valid card_670 ∧ Valid card_671 ∧ True :=
  ⟨valid_668, valid_669, valid_670, valid_671, True.intro⟩
