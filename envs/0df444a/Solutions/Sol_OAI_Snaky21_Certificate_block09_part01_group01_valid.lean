-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part01_group01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T13:28:07.095326+00:00
-- url     : https://prove2.me/submissions/f4ed740d-2876-4fcb-a1cd-022c40dcb8a0

import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_group00_valid
import Definitions.Def_Snaky21Data09
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part00_valid
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
theorem valid_2 : Valid card_2 := block00_valid.2.2.1
theorem valid_4 : Valid card_4 := block00_valid.2.2.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_16 : Valid card_16 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_17 : Valid card_17 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_27 : Valid card_27 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_41 : Valid card_41 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_48 : Valid card_48 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_63 : Valid card_63 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_64 : Valid card_64 := block01_valid.1
theorem valid_82 : Valid card_82 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_107 : Valid card_107 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_109 : Valid card_109 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_133 : Valid card_133 := block02_valid.2.2.2.2.2.1
theorem valid_140 : Valid card_140 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_163 : Valid card_163 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_197 : Valid card_197 := block03_valid.2.2.2.2.2.1
theorem valid_251 : Valid card_251 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_272 : Valid card_272 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_290 : Valid card_290 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_291 : Valid card_291 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_401 : Valid card_401 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_413 : Valid card_413 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_584 : Valid card_584 := block09_part00_valid.2.2.2.2.2.2.2.2.1
theorem valid_591 : Valid card_591 := block09_part00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_593 : Valid card_593 := block09_part01_group00_valid.2.1
theorem valid_594 : Valid card_594 := block09_part01_group00_valid.2.2.1
theorem valid_595 : Valid card_595 := block09_part01_group00_valid.2.2.2.1

theorem eq_inline_427 : inline_427 = combine (4, 5) [placed 7 (4, 5) card_2, placed 0 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_427 : Valid inline_427 := by
  rw [eq_inline_427]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_2
  subst c
  exact placed_valid 0 (1, 4) valid_5

theorem eq_inline_428 : inline_428 = combine (4, 2) [placed 0 (0, 1) card_2, inline_427] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_428 : Valid inline_428 := by
  rw [eq_inline_428]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact valid_inline_427

theorem eq_inline_429 : inline_429 = combine (4, 3) [placed 7 (4, 5) card_0, placed 2 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_429 : Valid inline_429 := by
  rw [eq_inline_429]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_0
  subst c
  exact placed_valid 2 (1, 4) valid_5

theorem eq_inline_430 : inline_430 = combine (4, 2) [placed 0 (0, 1) card_2, inline_429] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_430 : Valid inline_430 := by
  rw [eq_inline_430]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact valid_inline_429

theorem eq_inline_431 : inline_431 = combine (4, 2) [placed 0 (0, 1) card_2, placed 1 (2, 1) card_82] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_431 : Valid inline_431 := by
  rw [eq_inline_431]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact placed_valid 1 (2, 1) valid_82

theorem eq_inline_432 : inline_432 = combine (5, 4) [placed 5 (1, 4) card_6, placed 0 (0, 0) card_595, inline_431] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_432 : Valid inline_432 := by
  rw [eq_inline_432]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_595
  subst c
  exact valid_inline_431

theorem eq_card_596 : card_596 = combine (4, 4) [placed 2 (1, 5) card_197, inline_428, inline_430, inline_432] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_596 : Valid card_596 := by
  rw [eq_card_596]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_197
  rcases hc with rfl | hc
  · exact valid_inline_428
  rcases hc with rfl | hc
  · exact valid_inline_430
  subst c
  exact valid_inline_432

theorem eq_inline_433 : inline_433 = combine (5, 4) [placed 6 (6, 7) card_13, placed 0 (2, 2) card_109, placed 0 (2, 2) card_291] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_433 : Valid inline_433 := by
  rw [eq_inline_433]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_109
  subst c
  exact placed_valid 0 (2, 2) valid_291

theorem eq_inline_434 : inline_434 = combine (4, 2) [placed 7 (5, 5) card_5, placed 4 (5, 2) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_434 : Valid inline_434 := by
  rw [eq_inline_434]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 5) valid_5
  subst c
  exact placed_valid 4 (5, 2) valid_5

theorem eq_inline_435 : inline_435 = combine (5, 2) [placed 2 (5, 6) card_7, inline_434] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_435 : Valid inline_435 := by
  rw [eq_inline_435]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 6) valid_7
  subst c
  exact valid_inline_434

theorem eq_inline_436 : inline_436 = combine (6, 1) [placed 2 (2, 2) card_4, placed 5 (5, 5) card_4] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_436 : Valid inline_436 := by
  rw [eq_inline_436]
  apply combination_rule (6, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 2) valid_4
  subst c
  exact placed_valid 5 (5, 5) valid_4

theorem eq_inline_437 : inline_437 = combine (5, 2) [placed 4 (5, 2) card_5, inline_436] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_437 : Valid inline_437 := by
  rw [eq_inline_437]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_5
  subst c
  exact valid_inline_436

theorem eq_inline_438 : inline_438 = combine (4, 2) [placed 6 (5, 6) card_140, inline_437] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_438 : Valid inline_438 := by
  rw [eq_inline_438]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_140
  subst c
  exact valid_inline_437

theorem eq_inline_439 : inline_439 = combine (5, 4) [inline_435, inline_438, placed 1 (1, 2) card_596] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_439 : Valid inline_439 := by
  rw [eq_inline_439]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_435
  rcases hc with rfl | hc
  · exact valid_inline_438
  subst c
  exact placed_valid 1 (1, 2) valid_596

theorem eq_card_597 : card_597 = combine (5, 5) [placed 1 (1, 2) card_272, placed 5 (1, 6) card_290, placed 1 (0, 2) card_593, inline_433, inline_439] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_597 : Valid card_597 := by
  rw [eq_card_597]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_272
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_290
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_593
  rcases hc with rfl | hc
  · exact valid_inline_433
  subst c
  exact valid_inline_439

theorem eq_inline_440 : inline_440 = combine (5, 5) [placed 4 (6, 5) card_5, placed 4 (7, 3) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_440 : Valid inline_440 := by
  rw [eq_inline_440]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 5) valid_5
  subst c
  exact placed_valid 4 (7, 3) valid_133

theorem eq_inline_441 : inline_441 = combine (4, 5) [placed 5 (3, 8) card_0, inline_440] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_441 : Valid inline_441 := by
  rw [eq_inline_441]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_0
  subst c
  exact valid_inline_440

theorem eq_inline_442 : inline_442 = combine (3, 6) [placed 1 (3, 4) card_5, inline_441] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_442 : Valid inline_442 := by
  rw [eq_inline_442]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_5
  subst c
  exact valid_inline_441

theorem eq_inline_443 : inline_443 = combine (5, 5) [placed 4 (6, 5) card_5, placed 6 (7, 7) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_443 : Valid inline_443 := by
  rw [eq_inline_443]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 5) valid_5
  subst c
  exact placed_valid 6 (7, 7) valid_133

theorem eq_inline_444 : inline_444 = combine (4, 5) [placed 5 (3, 8) card_0, inline_443] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_444 : Valid inline_444 := by
  rw [eq_inline_444]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_0
  subst c
  exact valid_inline_443

theorem eq_inline_445 : inline_445 = combine (3, 6) [placed 1 (3, 4) card_5, inline_444] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_445 : Valid inline_445 := by
  rw [eq_inline_445]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_5
  subst c
  exact valid_inline_444

theorem eq_inline_446 : inline_446 = combine (5, 5) [placed 4 (6, 5) card_5, placed 5 (2, 6) card_413] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_446 : Valid inline_446 := by
  rw [eq_inline_446]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 5) valid_5
  subst c
  exact placed_valid 5 (2, 6) valid_413

theorem eq_inline_447 : inline_447 = combine (4, 5) [placed 5 (3, 8) card_0, inline_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_447 : Valid inline_447 := by
  rw [eq_inline_447]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_0
  subst c
  exact valid_inline_446

theorem eq_inline_448 : inline_448 = combine (3, 6) [placed 1 (3, 4) card_5, inline_447] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_448 : Valid inline_448 := by
  rw [eq_inline_448]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_5
  subst c
  exact valid_inline_447

theorem eq_card_598 : card_598 = combine (3, 5) [inline_442, inline_445, placed 1 (2, 4) card_584, placed 2 (2, 10) card_591, placed 4 (8, 1) card_594, inline_448, placed 0 (1, 2) card_597] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_598 : Valid card_598 := by
  rw [eq_card_598]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_442
  rcases hc with rfl | hc
  · exact valid_inline_445
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_584
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_591
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 1) valid_594
  rcases hc with rfl | hc
  · exact valid_inline_448
  subst c
  exact placed_valid 0 (1, 2) valid_597

theorem eq_inline_449 : inline_449 = combine (5, 6) [placed 0 (2, 5) card_5, placed 0 (4, 2) card_64] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_449 : Valid inline_449 := by
  rw [eq_inline_449]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_5
  subst c
  exact placed_valid 0 (4, 2) valid_64

theorem eq_inline_450 : inline_450 = combine (4, 4) [placed 6 (7, 5) card_0, placed 0 (4, 2) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_450 : Valid inline_450 := by
  rw [eq_inline_450]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 5) valid_0
  subst c
  exact placed_valid 0 (4, 2) valid_44

theorem eq_inline_451 : inline_451 = combine (6, 5) [placed 5 (2, 5) card_6, placed 5 (3, 5) card_16, inline_450] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_451 : Valid inline_451 := by
  rw [eq_inline_451]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_16
  subst c
  exact valid_inline_450

theorem eq_inline_452 : inline_452 = combine (5, 5) [placed 0 (2, 4) card_8, placed 1 (2, 4) card_17, placed 1 (2, 4) card_41, inline_449, inline_451] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_452 : Valid inline_452 := by
  rw [eq_inline_452]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_41
  rcases hc with rfl | hc
  · exact valid_inline_449
  subst c
  exact valid_inline_451

theorem eq_inline_453 : inline_453 = combine (2, 5) [placed 3 (3, 2) card_5, inline_452] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_453 : Valid inline_453 := by
  rw [eq_inline_453]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 2) valid_5
  subst c
  exact valid_inline_452

theorem eq_inline_454 : inline_454 = combine (4, 5) [placed 1 (3, 2) card_5, inline_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_454 : Valid inline_454 := by
  rw [eq_inline_454]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 2) valid_5
  subst c
  exact valid_inline_453

theorem eq_inline_455 : inline_455 = combine (3, 2) [placed 6 (4, 6) card_9, placed 7 (4, 5) card_251, inline_454] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_455 : Valid inline_455 := by
  rw [eq_inline_455]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_251
  subst c
  exact valid_inline_454

theorem eq_inline_456 : inline_456 = combine (3, 5) [placed 4 (4, 2) card_10, placed 0 (3, 2) card_27, placed 4 (4, 2) card_48, placed 4 (4, 2) card_63, inline_455] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_456 : Valid inline_456 := by
  rw [eq_inline_456]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_48
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_63
  subst c
  exact valid_inline_455

theorem eq_inline_457 : inline_457 = combine (3, 4) [placed 2 (0, 4) card_2, inline_456] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_457 : Valid inline_457 := by
  rw [eq_inline_457]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_2
  subst c
  exact valid_inline_456

theorem eq_card_599 : card_599 = combine (4, 3) [placed 5 (0, 4) card_107, placed 5 (0, 4) card_163, placed 2 (0, 7) card_401, inline_457] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_599 : Valid card_599 := by
  rw [eq_card_599]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_107
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_163
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_401
  subst c
  exact valid_inline_457


end OAI.Snaky21.Certificate

theorem solution : Valid card_596 ∧ Valid card_597 ∧ Valid card_598 ∧ Valid card_599 ∧ True :=
  ⟨valid_596, valid_597, valid_598, valid_599, True.intro⟩
