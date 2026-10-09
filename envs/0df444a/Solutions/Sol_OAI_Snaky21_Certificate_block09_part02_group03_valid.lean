-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part02_group03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:45:15.940677+00:00
-- url     : https://prove2.me/submissions/95a8d597-626b-4770-a83f-98f862a80fee

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part02_group00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part02_group02_valid
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
theorem valid_4 : Valid card_4 := block00_valid.2.2.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_17 : Valid card_17 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_23 : Valid card_23 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_27 : Valid card_27 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_35 : Valid card_35 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_37 : Valid card_37 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_41 : Valid card_41 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_57 : Valid card_57 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_61 : Valid card_61 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_133 : Valid card_133 := block02_valid.2.2.2.2.2.1
theorem valid_137 : Valid card_137 := block02_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_151 : Valid card_151 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_159 : Valid card_159 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_164 : Valid card_164 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_179 : Valid card_179 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_181 : Valid card_181 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_186 : Valid card_186 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_187 : Valid card_187 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_188 : Valid card_188 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_197 : Valid card_197 := block03_valid.2.2.2.2.2.1
theorem valid_206 : Valid card_206 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_211 : Valid card_211 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_233 : Valid card_233 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_238 : Valid card_238 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_293 : Valid card_293 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_322 : Valid card_322 := block05_valid.2.2.1
theorem valid_363 : Valid card_363 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_369 : Valid card_369 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_371 : Valid card_371 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_414 : Valid card_414 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_417 : Valid card_417 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_443 : Valid card_443 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_444 : Valid card_444 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_465 : Valid card_465 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_467 : Valid card_467 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_474 : Valid card_474 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_602 : Valid card_602 := block09_part01_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_603 : Valid card_603 := block09_part01_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_605 : Valid card_605 := block09_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_606 : Valid card_606 := block09_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_607 : Valid card_607 := block09_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_608 : Valid card_608 := block09_part02_group00_valid.1
theorem valid_610 : Valid card_610 := block09_part02_group00_valid.2.2.1
theorem valid_618 : Valid card_618 := block09_part02_group02_valid.2.2.1
theorem valid_619 : Valid card_619 := block09_part02_group02_valid.2.2.2.1

theorem eq_inline_521 : inline_521 = combine (3, 3) [placed 6 (4, 6) card_17, placed 6 (4, 6) card_37, placed 3 (4, 3) card_233] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_521 : Valid inline_521 := by
  rw [eq_inline_521]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_37
  subst c
  exact placed_valid 3 (4, 3) valid_233

theorem eq_card_620 : card_620 = combine (4, 5) [placed 3 (6, 3) card_57, placed 7 (6, 7) card_57, placed 3 (6, 3) card_293, placed 7 (6, 7) card_293, inline_521] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_620 : Valid card_620 := by
  rw [eq_card_620]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_293
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_293
  subst c
  exact valid_inline_521

theorem eq_inline_522 : inline_522 = combine (2, 3) [placed 7 (5, 4) card_15, placed 1 (1, 2) card_159, placed 6 (4, 6) card_164] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_522 : Valid inline_522 := by
  rw [eq_inline_522]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_159
  subst c
  exact placed_valid 6 (4, 6) valid_164

theorem eq_inline_523 : inline_523 = combine (1, 4) [placed 2 (0, 4) card_0, placed 2 (0, 6) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_523 : Valid inline_523 := by
  rw [eq_inline_523]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_0
  subst c
  exact placed_valid 2 (0, 6) valid_133

theorem eq_card_621 : card_621 = combine (2, 4) [placed 1 (0, 3) card_206, placed 3 (5, 2) card_238, placed 7 (5, 5) card_414, placed 6 (4, 6) card_417, inline_522, inline_523] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_621 : Valid card_621 := by
  rw [eq_card_621]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_206
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 2) valid_238
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 5) valid_414
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_417
  rcases hc with rfl | hc
  · exact valid_inline_522
  subst c
  exact valid_inline_523

theorem eq_inline_524 : inline_524 = combine (3, 6) [placed 4 (4, 3) card_41, placed 7 (6, 6) card_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_524 : Valid inline_524 := by
  rw [eq_inline_524]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_41
  subst c
  exact placed_valid 7 (6, 6) valid_56

theorem eq_inline_525 : inline_525 = combine (3, 6) [placed 7 (3, 6) card_4, placed 4 (4, 3) card_41] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_525 : Valid inline_525 := by
  rw [eq_inline_525]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_4
  subst c
  exact placed_valid 4 (4, 3) valid_41

theorem eq_inline_526 : inline_526 = combine (3, 2) [placed 7 (3, 5) card_5, placed 2 (3, 6) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_526 : Valid inline_526 := by
  rw [eq_inline_526]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 5) valid_5
  subst c
  exact placed_valid 2 (3, 6) valid_11

theorem eq_inline_527 : inline_527 = combine (2, 2) [placed 6 (3, 6) card_61, inline_525, inline_526] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_527 : Valid inline_527 := by
  rw [eq_inline_527]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_61
  rcases hc with rfl | hc
  · exact valid_inline_525
  subst c
  exact valid_inline_526

theorem eq_inline_528 : inline_528 = combine (4, 5) [placed 2 (3, 6) card_23, placed 4 (7, 1) card_621] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_528 : Valid inline_528 := by
  rw [eq_inline_528]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_23
  subst c
  exact placed_valid 4 (7, 1) valid_621

theorem eq_card_622 : card_622 = combine (4, 4) [placed 7 (6, 6) card_57, inline_524, inline_527, inline_528] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_622 : Valid card_622 := by
  rw [eq_card_622]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_57
  rcases hc with rfl | hc
  · exact valid_inline_524
  rcases hc with rfl | hc
  · exact valid_inline_527
  subst c
  exact valid_inline_528

theorem eq_inline_529 : inline_529 = combine (5, 5) [placed 4 (7, 3) card_188, placed 0 (4, 4) card_444, placed 2 (4, 9) card_606, placed 2 (4, 9) card_610] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_529 : Valid inline_529 := by
  rw [eq_inline_529]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_444
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 9) valid_606
  subst c
  exact placed_valid 2 (4, 9) valid_610

theorem eq_inline_530 : inline_530 = combine (5, 5) [placed 7 (7, 8) card_137, placed 7 (7, 8) card_181, placed 6 (8, 9) card_363, placed 7 (7, 8) card_474, placed 2 (4, 9) card_606] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_530 : Valid inline_530 := by
  rw [eq_inline_530]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 8) valid_137
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 8) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_363
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 8) valid_474
  subst c
  exact placed_valid 2 (4, 9) valid_606

theorem eq_inline_531 : inline_531 = combine (4, 7) [placed 4 (5, 6) card_27, placed 5 (4, 9) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_531 : Valid inline_531 := by
  rw [eq_inline_531]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 6) valid_27
  subst c
  exact placed_valid 5 (4, 9) valid_35

theorem eq_inline_532 : inline_532 = combine (5, 9) [placed 2 (4, 10) card_9, placed 4 (8, 5) card_151, placed 4 (6, 4) card_186, placed 4 (5, 4) card_187, inline_531] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_532 : Valid inline_532 := by
  rw [eq_inline_532]
  apply combination_rule (5, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 10) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 5) valid_151
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 4) valid_186
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 4) valid_187
  subst c
  exact valid_inline_531

theorem eq_inline_533 : inline_533 = combine (5, 5) [placed 5 (3, 9) card_179, placed 5 (4, 8) card_371, placed 2 (4, 9) card_443] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_533 : Valid inline_533 := by
  rw [eq_inline_533]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 9) valid_179
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_371
  subst c
  exact placed_valid 2 (4, 9) valid_443

theorem eq_inline_534 : inline_534 = combine (5, 8) [placed 4 (6, 4) card_12, placed 4 (7, 4) card_188, placed 4 (8, 4) card_211, inline_532, placed 1 (2, 5) card_619, inline_533, placed 4 (8, 2) card_620] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_534 : Valid inline_534 := by
  rw [eq_inline_534]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 4) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 4) valid_211
  rcases hc with rfl | hc
  · exact valid_inline_532
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_619
  rcases hc with rfl | hc
  · exact valid_inline_533
  subst c
  exact placed_valid 4 (8, 2) valid_620

theorem eq_inline_535 : inline_535 = combine (5, 5) [placed 5 (3, 9) card_179, placed 5 (4, 8) card_197, placed 0 (4, 4) card_465] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_535 : Valid inline_535 := by
  rw [eq_inline_535]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 9) valid_179
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_197
  subst c
  exact placed_valid 0 (4, 4) valid_465

theorem eq_inline_536 : inline_536 = combine (5, 8) [placed 0 (4, 4) card_12, placed 1 (1, 5) card_322, placed 2 (4, 11) card_369, placed 1 (2, 5) card_435, inline_535, placed 6 (8, 11) card_622] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_536 : Valid inline_536 := by
  rw [eq_inline_536]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 5) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 11) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_435
  rcases hc with rfl | hc
  · exact valid_inline_535
  subst c
  exact placed_valid 6 (8, 11) valid_622

theorem eq_card_623 : card_623 = combine (5, 6) [placed 6 (9, 11) card_467, placed 1 (0, 3) card_602, placed 4 (6, 3) card_603, placed 3 (8, 4) card_605, placed 6 (9, 11) card_607, placed 6 (9, 11) card_608, inline_529, placed 6 (10, 10) card_618, inline_530, inline_534, inline_536] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_623 : Valid card_623 := by
  rw [eq_card_623]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 11) valid_467
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_602
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_603
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 11) valid_607
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 11) valid_608
  rcases hc with rfl | hc
  · exact valid_inline_529
  rcases hc with rfl | hc
  · exact placed_valid 6 (10, 10) valid_618
  rcases hc with rfl | hc
  · exact valid_inline_530
  rcases hc with rfl | hc
  · exact valid_inline_534
  subst c
  exact valid_inline_536


end OAI.Snaky21.Certificate

theorem solution : Valid card_620 ∧ Valid card_621 ∧ Valid card_622 ∧ Valid card_623 ∧ True :=
  ⟨valid_620, valid_621, valid_622, valid_623, True.intro⟩
