-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part02_group01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:40:45.358993+00:00
-- url     : https://prove2.me/submissions/3b357272-6934-49f3-9f10-9b18ae4d9fc3

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part02_group00_valid
import Definitions.Def_Snaky21Data09
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_valid
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
theorem valid_1 : Valid card_1 := block00_valid.2.1
theorem valid_3 : Valid card_3 := block00_valid.2.2.2.1
theorem valid_4 : Valid card_4 := block00_valid.2.2.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_20 : Valid card_20 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_36 : Valid card_36 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_43 : Valid card_43 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_50 : Valid card_50 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_54 : Valid card_54 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_57 : Valid card_57 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_66 : Valid card_66 := block01_valid.2.2.1
theorem valid_68 : Valid card_68 := block01_valid.2.2.2.2.1
theorem valid_104 : Valid card_104 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_116 : Valid card_116 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_134 : Valid card_134 := block02_valid.2.2.2.2.2.2.1
theorem valid_139 : Valid card_139 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_148 : Valid card_148 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_180 : Valid card_180 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_276 : Valid card_276 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_329 : Valid card_329 := block05_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_362 : Valid card_362 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_402 : Valid card_402 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_409 : Valid card_409 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_425 : Valid card_425 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_495 : Valid card_495 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_558 : Valid card_558 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_561 : Valid card_561 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_611 : Valid card_611 := block09_part02_group00_valid.2.2.2.1

theorem eq_inline_493 : inline_493 = combine (1, 2) [placed 0 (1, 1) card_6, placed 4 (1, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_493 : Valid inline_493 := by
  rw [eq_inline_493]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_6
  subst c
  exact placed_valid 4 (1, 1) valid_6

theorem eq_inline_494 : inline_494 = combine (0, 2) [placed 7 (1, 6) card_0, placed 1 (0, 1) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_494 : Valid inline_494 := by
  rw [eq_inline_494]
  apply combination_rule (0, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 6) valid_0
  subst c
  exact placed_valid 1 (0, 1) valid_3

theorem eq_inline_495 : inline_495 = combine (1, 2) [placed 7 (1, 5) card_4, placed 0 (1, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_495 : Valid inline_495 := by
  rw [eq_inline_495]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_4
  subst c
  exact placed_valid 0 (1, 1) valid_6

theorem eq_inline_496 : inline_496 = combine (1, 5) [inline_493, inline_494, inline_495] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_496 : Valid inline_496 := by
  rw [eq_inline_496]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_493
  rcases hc with rfl | hc
  · exact valid_inline_494
  subst c
  exact valid_inline_495

theorem eq_card_612 : card_612 = combine (1, 4) [placed 6 (1, 4) card_36, placed 0 (0, 0) card_50, placed 0 (0, 0) card_54, inline_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_612 : Valid card_612 := by
  rw [eq_card_612]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 4) valid_36
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_54
  subst c
  exact valid_inline_496

theorem eq_card_613 : card_613 = combine (2, 5) [placed 0 (1, 0) card_104, placed 4 (2, 0) card_329, placed 2 (1, 8) card_409, placed 0 (1, 2) card_612, placed 2 (1, 6) card_612, placed 6 (2, 6) card_612] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_613 : Valid card_613 := by
  rw [eq_card_613]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_104
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_329
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_409
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_612
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_612
  subst c
  exact placed_valid 6 (2, 6) valid_612

theorem eq_inline_497 : inline_497 = combine (2, 4) [placed 0 (0, 4) card_1, placed 2 (2, 6) card_425] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_497 : Valid inline_497 := by
  rw [eq_inline_497]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 4) valid_1
  subst c
  exact placed_valid 2 (2, 6) valid_425

theorem eq_inline_498 : inline_498 = combine (4, 3) [placed 5 (0, 4) card_68, placed 2 (3, 8) card_495] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_498 : Valid inline_498 := by
  rw [eq_inline_498]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_68
  subst c
  exact placed_valid 2 (3, 8) valid_495

theorem eq_inline_499 : inline_499 = combine (4, 4) [placed 2 (3, 6) card_66, placed 0 (3, 2) card_66] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_499 : Valid inline_499 := by
  rw [eq_inline_499]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_66
  subst c
  exact placed_valid 0 (3, 2) valid_66

theorem eq_inline_500 : inline_500 = combine (4, 3) [placed 5 (0, 4) card_68, inline_499] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_500 : Valid inline_500 := by
  rw [eq_inline_500]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_68
  subst c
  exact valid_inline_499

theorem eq_inline_501 : inline_501 = combine (4, 3) [placed 5 (0, 4) card_68, placed 2 (4, 6) card_612] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_501 : Valid inline_501 := by
  rw [eq_inline_501]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_68
  subst c
  exact placed_valid 2 (4, 6) valid_612

theorem eq_inline_502 : inline_502 = combine (5, 3) [placed 2 (3, 8) card_276, inline_497, placed 2 (3, 9) card_611, inline_498, inline_500, inline_501] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_502 : Valid inline_502 := by
  rw [eq_inline_502]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_276
  rcases hc with rfl | hc
  · exact valid_inline_497
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_611
  rcases hc with rfl | hc
  · exact valid_inline_498
  rcases hc with rfl | hc
  · exact valid_inline_500
  subst c
  exact valid_inline_501

theorem eq_card_614 : card_614 = combine (5, 5) [placed 1 (0, 4) card_68, placed 2 (3, 7) card_558, inline_502] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_614 : Valid card_614 := by
  rw [eq_card_614]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_68
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_558
  subst c
  exact valid_inline_502

theorem eq_inline_503 : inline_503 = combine (4, 3) [placed 2 (4, 7) card_11, placed 2 (3, 6) card_20, placed 0 (3, 2) card_402] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_503 : Valid inline_503 := by
  rw [eq_inline_503]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_20
  subst c
  exact placed_valid 0 (3, 2) valid_402

theorem eq_inline_504 : inline_504 = combine (4, 4) [placed 6 (7, 5) card_0, inline_503] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_504 : Valid inline_504 := by
  rw [eq_inline_504]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 5) valid_0
  subst c
  exact valid_inline_503

theorem eq_inline_505 : inline_505 = combine (6, 5) [placed 2 (3, 5) card_5, inline_504] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_505 : Valid inline_505 := by
  rw [eq_inline_505]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_5
  subst c
  exact valid_inline_504

theorem eq_inline_506 : inline_506 = combine (6, 4) [placed 5 (2, 5) card_139, placed 3 (6, 4) card_148, inline_505] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_506 : Valid inline_506 := by
  rw [eq_inline_506]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_139
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_148
  subst c
  exact valid_inline_505

theorem eq_inline_507 : inline_507 = combine (4, 6) [placed 0 (3, 3) card_43, placed 2 (2, 8) card_57, inline_506] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_507 : Valid inline_507 := by
  rw [eq_inline_507]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_43
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_57
  subst c
  exact valid_inline_506

theorem eq_inline_508 : inline_508 = combine (5, 5) [placed 4 (6, 2) card_116, placed 2 (2, 7) card_134, placed 2 (2, 7) card_180, placed 2 (2, 8) card_435, placed 2 (3, 7) card_558, placed 0 (2, 0) card_561, inline_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_508 : Valid inline_508 := by
  rw [eq_inline_508]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_558
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_561
  subst c
  exact valid_inline_507

theorem eq_card_615 : card_615 = combine (4, 5) [placed 0 (0, 1) card_362, placed 0 (0, 0) card_614, inline_508] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_615 : Valid card_615 := by
  rw [eq_card_615]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_362
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_614
  subst c
  exact valid_inline_508


end OAI.Snaky21.Certificate

theorem solution : Valid card_612 ∧ Valid card_613 ∧ Valid card_614 ∧ Valid card_615 ∧ True :=
  ⟨valid_612, valid_613, valid_614, valid_615, True.intro⟩
