-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part03_group00_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:47:32.980384+00:00
-- url     : https://prove2.me/submissions/8882bf45-d4cc-4d04-aa77-51df71092d07

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_valid
import Definitions.Def_Snaky21Data09
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part02_valid
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
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_34 : Valid card_34 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_38 : Valid card_38 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_50 : Valid card_50 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_54 : Valid card_54 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_59 : Valid card_59 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_64 : Valid card_64 := block01_valid.1
theorem valid_73 : Valid card_73 := block01_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_82 : Valid card_82 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_97 : Valid card_97 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_98 : Valid card_98 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_105 : Valid card_105 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_125 : Valid card_125 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_179 : Valid card_179 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_205 : Valid card_205 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_294 : Valid card_294 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_315 : Valid card_315 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_317 : Valid card_317 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_323 : Valid card_323 := block05_valid.2.2.2.1
theorem valid_336 : Valid card_336 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_412 : Valid card_412 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_413 : Valid card_413 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_430 : Valid card_430 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_449 : Valid card_449 := block07_valid.2.1
theorem valid_454 : Valid card_454 := block07_valid.2.2.2.2.2.2.1
theorem valid_455 : Valid card_455 := block07_valid.2.2.2.2.2.2.2.1
theorem valid_472 : Valid card_472 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_478 : Valid card_478 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_519 : Valid card_519 := block08_valid.2.2.2.2.2.2.2.1
theorem valid_545 : Valid card_545 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_592 : Valid card_592 := block09_part01_valid.1
theorem valid_603 : Valid card_603 := block09_part01_valid.2.2.2.2.2.2.2.2.2.2.2.1


theorem eq_inline_537 : inline_537 = combine (4, 3) [placed 5 (0, 4) card_64, placed 4 (4, 2) card_315] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_537 : Valid inline_537 := by
  rw [eq_inline_537]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_64
  subst c
  exact placed_valid 4 (4, 2) valid_315

theorem eq_inline_538 : inline_538 = combine (3, 3) [placed 6 (4, 6) card_10, placed 0 (3, 2) card_52, placed 2 (0, 6) card_82, inline_537] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_538 : Valid inline_538 := by
  rw [eq_inline_538]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_82
  subst c
  exact valid_inline_537

theorem eq_card_624 : card_624 = combine (3, 4) [placed 1 (0, 4) card_54, placed 0 (2, 0) card_545, inline_538] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_624 : Valid card_624 := by
  rw [eq_card_624]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_545
  subst c
  exact valid_inline_538

theorem eq_inline_539 : inline_539 = combine (3, 1) [placed 7 (6, 4) card_56, placed 4 (4, 0) card_73] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_539 : Valid inline_539 := by
  rw [eq_inline_539]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_56
  subst c
  exact placed_valid 4 (4, 0) valid_73

theorem eq_inline_540 : inline_540 = combine (3, 4) [placed 4 (4, 1) card_10, placed 0 (0, 1) card_82, inline_539] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_540 : Valid inline_540 := by
  rw [eq_inline_540]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_82
  subst c
  exact valid_inline_539

theorem eq_inline_541 : inline_541 = combine (3, 3) [placed 5 (0, 3) card_54, placed 3 (6, 1) card_294, placed 1 (0, 0) card_449, inline_540] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_541 : Valid inline_541 := by
  rw [eq_inline_541]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 1) valid_294
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_449
  subst c
  exact valid_inline_540

theorem eq_card_625 : card_625 = combine (3, 2) [placed 5 (0, 3) card_50, placed 5 (0, 3) card_125, placed 3 (5, 1) card_454, placed 0 (1, 1) card_455, inline_541] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_625 : Valid card_625 := by
  rw [eq_card_625]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 1) valid_454
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_455
  subst c
  exact valid_inline_541

theorem eq_inline_542 : inline_542 = combine (2, 5) [placed 0 (2, 5) card_5, placed 6 (5, 6) card_38] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_542 : Valid inline_542 := by
  rw [eq_inline_542]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_5
  subst c
  exact placed_valid 6 (5, 6) valid_38

theorem eq_inline_543 : inline_543 = combine (4, 5) [placed 2 (2, 9) card_317, inline_542, placed 0 (2, 2) card_519] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_543 : Valid inline_543 := by
  rw [eq_inline_543]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_317
  rcases hc with rfl | hc
  · exact valid_inline_542
  subst c
  exact placed_valid 0 (2, 2) valid_519

theorem eq_inline_544 : inline_544 = combine (2, 5) [placed 6 (5, 6) card_5, placed 1 (1, 5) card_412] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_544 : Valid inline_544 := by
  rw [eq_inline_544]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_5
  subst c
  exact placed_valid 1 (1, 5) valid_412

theorem eq_inline_545 : inline_545 = combine (4, 6) [placed 5 (1, 6) card_11, placed 1 (2, 5) card_336, inline_544] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_545 : Valid inline_545 := by
  rw [eq_inline_545]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_336
  subst c
  exact valid_inline_544

theorem eq_card_626 : card_626 = combine (5, 6) [placed 4 (6, 2) card_323, placed 0 (2, 2) card_430, placed 7 (6, 6) card_592, inline_543, inline_545] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_626 : Valid card_626 := by
  rw [eq_card_626]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_323
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_430
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_592
  rcases hc with rfl | hc
  · exact valid_inline_543
  subst c
  exact valid_inline_545

theorem eq_inline_546 : inline_546 = combine (4, 4) [placed 2 (3, 4) card_5, placed 4 (7, 2) card_472] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_546 : Valid inline_546 := by
  rw [eq_inline_546]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_5
  subst c
  exact placed_valid 4 (7, 2) valid_472

theorem eq_inline_547 : inline_547 = combine (5, 3) [placed 7 (6, 6) card_38, placed 6 (6, 7) card_205] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_547 : Valid inline_547 := by
  rw [eq_inline_547]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_38
  subst c
  exact placed_valid 6 (6, 7) valid_205

theorem eq_inline_548 : inline_548 = combine (5, 5) [placed 5 (5, 7) card_0, inline_547] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_548 : Valid inline_548 := by
  rw [eq_inline_548]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 7) valid_0
  subst c
  exact valid_inline_547

theorem eq_inline_549 : inline_549 = combine (5, 3) [placed 7 (6, 6) card_38, placed 5 (3, 7) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_549 : Valid inline_549 := by
  rw [eq_inline_549]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_38
  subst c
  exact placed_valid 5 (3, 7) valid_179

theorem eq_inline_550 : inline_550 = combine (5, 5) [placed 5 (5, 7) card_0, inline_549] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_550 : Valid inline_550 := by
  rw [eq_inline_550]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 7) valid_0
  subst c
  exact valid_inline_549

theorem eq_inline_551 : inline_551 = combine (5, 7) [placed 4 (6, 3) card_50, placed 4 (6, 3) card_97, placed 0 (5, 3) card_98, placed 2 (4, 8) card_454, placed 1 (4, 4) card_455, placed 3 (10, 3) card_624] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_551 : Valid inline_551 := by
  rw [eq_inline_551]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_97
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_98
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_454
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_455
  subst c
  exact placed_valid 3 (10, 3) valid_624

theorem eq_inline_552 : inline_552 = combine (5, 3) [placed 7 (6, 6) card_38, placed 0 (4, 2) card_413] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_552 : Valid inline_552 := by
  rw [eq_inline_552]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_38
  subst c
  exact placed_valid 0 (4, 2) valid_413

theorem eq_inline_553 : inline_553 = combine (5, 5) [placed 5 (5, 7) card_0, inline_552] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_553 : Valid inline_553 := by
  rw [eq_inline_553]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 7) valid_0
  subst c
  exact valid_inline_552

theorem eq_inline_554 : inline_554 = combine (6, 6) [placed 3 (9, 3) card_59, placed 4 (6, 2) card_105, placed 5 (2, 7) card_323, placed 1 (2, 5) card_603] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_554 : Valid inline_554 := by
  rw [eq_inline_554]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 3) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_105
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_323
  subst c
  exact placed_valid 1 (2, 5) valid_603

theorem eq_inline_555 : inline_555 = combine (5, 6) [inline_548, inline_550, inline_551, placed 1 (0, 1) card_626, inline_553, inline_554] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_555 : Valid inline_555 := by
  rw [eq_inline_555]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_548
  rcases hc with rfl | hc
  · exact valid_inline_550
  rcases hc with rfl | hc
  · exact valid_inline_551
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_626
  rcases hc with rfl | hc
  · exact valid_inline_553
  subst c
  exact valid_inline_554

theorem eq_card_627 : card_627 = combine (5, 4) [placed 7 (7, 4) card_34, placed 0 (2, 2) card_478, inline_546, inline_555] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_627 : Valid card_627 := by
  rw [eq_card_627]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 4) valid_34
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_478
  rcases hc with rfl | hc
  · exact valid_inline_546
  subst c
  exact valid_inline_555


end OAI.Snaky21.Certificate

theorem solution : Valid card_624 ∧ Valid card_625 ∧ Valid card_626 ∧ Valid card_627 ∧ True :=
  ⟨valid_624, valid_625, valid_626, valid_627, True.intro⟩
