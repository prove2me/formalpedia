-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part01_group00_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:14:27.040459+00:00
-- url     : https://prove2.me/submissions/04d9c828-8b57-4a3f-ad3c-4f22034016a1

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
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
theorem valid_1 : Valid card_1 := block00_valid.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_20 : Valid card_20 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_27 : Valid card_27 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_29 : Valid card_29 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_50 : Valid card_50 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_54 : Valid card_54 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_65 : Valid card_65 := block01_valid.2.1
theorem valid_71 : Valid card_71 := block01_valid.2.2.2.2.2.2.2.1
theorem valid_79 : Valid card_79 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_85 : Valid card_85 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_117 : Valid card_117 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_125 : Valid card_125 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_134 : Valid card_134 := block02_valid.2.2.2.2.2.2.1
theorem valid_180 : Valid card_180 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_248 : Valid card_248 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_284 : Valid card_284 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_300 : Valid card_300 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_314 : Valid card_314 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_337 : Valid card_337 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_341 : Valid card_341 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_345 : Valid card_345 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_378 : Valid card_378 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_411 : Valid card_411 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_436 : Valid card_436 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_445 : Valid card_445 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_449 : Valid card_449 := block07_valid.2.1
theorem valid_478 : Valid card_478 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_482 : Valid card_482 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_508 : Valid card_508 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_510 : Valid card_510 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_537 : Valid card_537 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_558 : Valid card_558 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_605 : Valid card_605 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_631 : Valid card_631 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_644 : Valid card_644 := block10_part00_valid.2.2.2.2.1
theorem valid_645 : Valid card_645 := block10_part00_valid.2.2.2.2.2.1
theorem valid_647 : Valid card_647 := block10_part00_valid.2.2.2.2.2.2.2.1
theorem valid_650 : Valid card_650 := block10_part00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_651 : Valid card_651 := block10_part00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_652 : Valid card_652 := block10_part00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_653 : Valid card_653 := block10_part00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_654 : Valid card_654 := block10_part00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem eq_inline_620 : inline_620 = combine (5, 4) [placed 1 (2, 3) card_117, placed 5 (3, 7) card_134, placed 5 (3, 7) card_180, placed 6 (6, 9) card_337, placed 6 (8, 9) card_341, placed 5 (2, 7) card_435, placed 5 (3, 6) card_558] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_620 : Valid inline_620 := by
  rw [eq_inline_620]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_117
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 9) valid_337
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_341
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_435
  subst c
  exact placed_valid 5 (3, 6) valid_558

theorem eq_inline_621 : inline_621 = combine (4, 5) [placed 0 (2, 5) card_1, placed 1 (1, 2) card_651] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_621 : Valid inline_621 := by
  rw [eq_inline_621]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_1
  subst c
  exact placed_valid 1 (1, 2) valid_651

theorem eq_inline_622 : inline_622 = combine (4, 5) [placed 0 (2, 5) card_1, placed 2 (3, 9) card_652] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_622 : Valid inline_622 := by
  rw [eq_inline_622]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_1
  subst c
  exact placed_valid 2 (3, 9) valid_652

theorem eq_inline_623 : inline_623 = combine (5, 5) [placed 6 (7, 9) card_248, placed 6 (7, 9) card_300, placed 6 (8, 9) card_436, placed 5 (2, 8) card_449, placed 5 (2, 8) card_510, inline_620, inline_621, inline_622] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_623 : Valid inline_623 := by
  rw [eq_inline_623]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_248
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_300
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_436
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_449
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_510
  rcases hc with rfl | hc
  · exact valid_inline_620
  rcases hc with rfl | hc
  · exact valid_inline_621
  subst c
  exact valid_inline_622

theorem eq_card_656 : card_656 = combine (6, 6) [placed 0 (3, 3) card_508, placed 2 (3, 9) card_508, placed 0 (3, 3) card_605, placed 2 (3, 9) card_605, placed 3 (10, 2) card_644, placed 3 (10, 2) card_645, placed 3 (10, 2) card_647, placed 0 (2, 1) card_650, placed 2 (2, 11) card_650, inline_623, placed 3 (9, 3) card_654] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_656 : Valid card_656 := by
  rw [eq_card_656]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_644
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_645
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_647
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 11) valid_650
  rcases hc with rfl | hc
  · exact valid_inline_623
  subst c
  exact placed_valid 3 (9, 3) valid_654

theorem eq_inline_624 : inline_624 = combine (2, 4) [placed 5 (1, 4) card_54, placed 4 (5, 1) card_79] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_624 : Valid inline_624 := by
  rw [eq_inline_624]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_54
  subst c
  exact placed_valid 4 (5, 1) valid_79

theorem eq_inline_625 : inline_625 = combine (4, 2) [placed 1 (1, 2) card_54, placed 4 (5, 1) card_71, placed 1 (2, 1) card_345] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_625 : Valid inline_625 := by
  rw [eq_inline_625]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_71
  subst c
  exact placed_valid 1 (2, 1) valid_345

theorem eq_inline_626 : inline_626 = combine (6, 3) [placed 2 (3, 4) card_5, placed 2 (3, 5) card_445] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_626 : Valid inline_626 := by
  rw [eq_inline_626]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_5
  subst c
  exact placed_valid 2 (3, 5) valid_445

theorem eq_inline_627 : inline_627 = combine (6, 4) [placed 1 (3, 3) card_20, placed 5 (3, 4) card_29, inline_626] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_627 : Valid inline_627 := by
  rw [eq_inline_627]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_29
  subst c
  exact valid_inline_626

theorem eq_inline_628 : inline_628 = combine (3, 4) [placed 5 (2, 4) card_15, placed 1 (1, 3) card_65, inline_627] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_628 : Valid inline_628 := by
  rw [eq_inline_628]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_65
  subst c
  exact valid_inline_627

theorem eq_inline_629 : inline_629 = combine (5, 4) [placed 3 (8, 2) card_85, placed 2 (3, 7) card_85, placed 2 (4, 7) card_411, placed 3 (8, 2) card_537, inline_628] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_629 : Valid inline_629 := by
  rw [eq_inline_629]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 2) valid_85
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_85
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_411
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 2) valid_537
  subst c
  exact valid_inline_628

theorem eq_inline_630 : inline_630 = combine (4, 4) [placed 1 (1, 1) card_510, placed 0 (1, 0) card_631, placed 1 (1, 0) card_653, inline_624, inline_625, inline_629] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_630 : Valid inline_630 := by
  rw [eq_inline_630]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_510
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_631
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_653
  rcases hc with rfl | hc
  · exact valid_inline_624
  rcases hc with rfl | hc
  · exact valid_inline_625
  subst c
  exact valid_inline_629

theorem eq_card_657 : card_657 = combine (4, 3) [placed 1 (1, 2) card_50, placed 1 (1, 2) card_125, placed 0 (1, 1) card_478, placed 0 (1, 1) card_482, inline_630] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_657 : Valid card_657 := by
  rw [eq_card_657]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_478
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_482
  subst c
  exact valid_inline_630

theorem eq_inline_631 : inline_631 = combine (2, 6) [placed 1 (1, 3) card_314, placed 5 (0, 6) card_378] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_631 : Valid inline_631 := by
  rw [eq_inline_631]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_314
  subst c
  exact placed_valid 5 (0, 6) valid_378

theorem eq_card_658 : card_658 = combine (2, 3) [placed 6 (2, 6) card_27, placed 4 (2, 2) card_52, placed 2 (1, 9) card_284, inline_631] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_658 : Valid card_658 := by
  rw [eq_card_658]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_284
  subst c
  exact valid_inline_631

theorem eq_card_659 : card_659 = combine (3, 4) [placed 2 (0, 5) card_5, placed 0 (1, 0) card_658] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_659 : Valid card_659 := by
  rw [eq_card_659]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_658


end OAI.Snaky21.Certificate

theorem solution : Valid card_656 ∧ Valid card_657 ∧ Valid card_658 ∧ Valid card_659 ∧ True :=
  ⟨valid_656, valid_657, valid_658, valid_659, True.intro⟩
