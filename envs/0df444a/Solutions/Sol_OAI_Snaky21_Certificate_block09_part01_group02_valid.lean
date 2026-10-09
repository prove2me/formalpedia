-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part01_group02_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:32:01.948976+00:00
-- url     : https://prove2.me/submissions/075ad753-fee3-4682-8f66-8102ecc7049f

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_group01_valid
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
theorem valid_1 : Valid card_1 := block00_valid.2.1
theorem valid_2 : Valid card_2 := block00_valid.2.2.1
theorem valid_3 : Valid card_3 := block00_valid.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_18 : Valid card_18 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_20 : Valid card_20 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_23 : Valid card_23 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_29 : Valid card_29 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_31 : Valid card_31 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_35 : Valid card_35 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_55 : Valid card_55 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_59 : Valid card_59 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_64 : Valid card_64 := block01_valid.1
theorem valid_66 : Valid card_66 := block01_valid.2.2.1
theorem valid_72 : Valid card_72 := block01_valid.2.2.2.2.2.2.2.2.1
theorem valid_94 : Valid card_94 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_107 : Valid card_107 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_119 : Valid card_119 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_157 : Valid card_157 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_163 : Valid card_163 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_189 : Valid card_189 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_247 : Valid card_247 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_320 : Valid card_320 := block05_valid.1
theorem valid_367 : Valid card_367 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_381 : Valid card_381 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_383 : Valid card_383 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_406 : Valid card_406 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_427 : Valid card_427 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_457 : Valid card_457 := block07_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_496 : Valid card_496 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_497 : Valid card_497 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_498 : Valid card_498 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_499 : Valid card_499 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_500 : Valid card_500 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_501 : Valid card_501 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_545 : Valid card_545 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_553 : Valid card_553 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_555 : Valid card_555 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_556 : Valid card_556 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_557 : Valid card_557 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_564 : Valid card_564 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_568 : Valid card_568 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_573 : Valid card_573 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_574 : Valid card_574 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_583 : Valid card_583 := block09_part00_valid.2.2.2.2.2.2.2.1

theorem valid_598 : Valid card_598 := block09_part01_group01_valid.2.2.1
theorem valid_599 : Valid card_599 := block09_part01_group01_valid.2.2.2.1

theorem eq_inline_458 : inline_458 = combine (3, 5) [placed 0 (2, 2) card_20, placed 5 (0, 5) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_458 : Valid inline_458 := by
  rw [eq_inline_458]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_20
  subst c
  exact placed_valid 5 (0, 5) valid_55

theorem eq_card_600 : card_600 = combine (3, 2) [placed 6 (3, 5) card_23, inline_458] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_600 : Valid card_600 := by
  rw [eq_card_600]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 5) valid_23
  subst c
  exact valid_inline_458

theorem eq_inline_459 : inline_459 = combine (3, 5) [placed 0 (3, 2) card_29, placed 7 (4, 5) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_459 : Valid inline_459 := by
  rw [eq_inline_459]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_29
  subst c
  exact placed_valid 7 (4, 5) valid_35

theorem eq_inline_460 : inline_460 = combine (4, 4) [inline_459, placed 1 (1, 2) card_499, placed 0 (0, 1) card_501] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_460 : Valid inline_460 := by
  rw [eq_inline_460]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_459
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_499
  subst c
  exact placed_valid 0 (0, 1) valid_501

theorem eq_inline_461 : inline_461 = combine (5, 2) [placed 0 (3, 1) card_66, placed 1 (3, 2) card_94] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_461 : Valid inline_461 := by
  rw [eq_inline_461]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_66
  subst c
  exact placed_valid 1 (3, 2) valid_94

theorem eq_inline_462 : inline_462 = combine (4, 2) [placed 2 (3, 5) card_15, inline_461] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_462 : Valid inline_462 := by
  rw [eq_inline_462]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_15
  subst c
  exact valid_inline_461

theorem eq_inline_463 : inline_463 = combine (6, 3) [placed 4 (6, 3) card_1, inline_462] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_463 : Valid inline_463 := by
  rw [eq_inline_463]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_1
  subst c
  exact valid_inline_462

theorem eq_inline_464 : inline_464 = combine (2, 4) [placed 4 (4, 4) card_3, inline_463] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_464 : Valid inline_464 := by
  rw [eq_inline_464]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 4) valid_3
  subst c
  exact valid_inline_463

theorem eq_inline_465 : inline_465 = combine (2, 4) [placed 4 (4, 4) card_3, placed 0 (2, 2) card_72] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_465 : Valid inline_465 := by
  rw [eq_inline_465]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 4) valid_3
  subst c
  exact placed_valid 0 (2, 2) valid_72

theorem eq_inline_466 : inline_466 = combine (4, 4) [placed 2 (3, 6) card_406, placed 1 (1, 2) card_499, inline_464, placed 2 (1, 7) card_600, inline_465] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_466 : Valid inline_466 := by
  rw [eq_inline_466]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_406
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_499
  rcases hc with rfl | hc
  · exact valid_inline_464
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_600
  subst c
  exact valid_inline_465

theorem eq_inline_467 : inline_467 = combine (4, 4) [placed 2 (3, 6) card_406, placed 0 (0, 1) card_501] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_467 : Valid inline_467 := by
  rw [eq_inline_467]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_406
  subst c
  exact placed_valid 0 (0, 1) valid_501

theorem eq_card_601 : card_601 = combine (4, 3) [placed 0 (0, 1) card_247, inline_460, inline_466, inline_467] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_601 : Valid card_601 := by
  rw [eq_card_601]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_247
  rcases hc with rfl | hc
  · exact valid_inline_460
  rcases hc with rfl | hc
  · exact valid_inline_466
  subst c
  exact valid_inline_467

theorem eq_inline_468 : inline_468 = combine (5, 8) [placed 0 (3, 4) card_320, placed 5 (2, 8) card_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_468 : Valid inline_468 := by
  rw [eq_inline_468]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_320
  subst c
  exact placed_valid 5 (2, 8) valid_496

theorem eq_inline_469 : inline_469 = combine (6, 8) [placed 2 (3, 11) card_59, placed 5 (2, 8) card_497, inline_468, placed 0 (3, 3) card_555] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_469 : Valid inline_469 := by
  rw [eq_inline_469]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 11) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_497
  rcases hc with rfl | hc
  · exact valid_inline_468
  subst c
  exact placed_valid 0 (3, 3) valid_555

theorem eq_inline_470 : inline_470 = combine (6, 8) [placed 2 (3, 8) card_2, placed 2 (5, 12) card_545] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_470 : Valid inline_470 := by
  rw [eq_inline_470]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_2
  subst c
  exact placed_valid 2 (5, 12) valid_545

theorem eq_inline_471 : inline_471 = combine (7, 7) [placed 5 (3, 8) card_107, placed 5 (3, 8) card_163, placed 2 (3, 11) card_556, inline_470] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_471 : Valid inline_471 := by
  rw [eq_inline_471]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_107
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_163
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 11) valid_556
  subst c
  exact valid_inline_470

theorem eq_inline_472 : inline_472 = combine (6, 5) [placed 0 (3, 4) card_157, placed 4 (6, 3) card_383] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_472 : Valid inline_472 := by
  rw [eq_inline_472]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_157
  subst c
  exact placed_valid 4 (6, 3) valid_383

theorem eq_inline_473 : inline_473 = combine (6, 6) [placed 0 (5, 5) card_18, placed 7 (7, 8) card_381] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_473 : Valid inline_473 := by
  rw [eq_inline_473]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_18
  subst c
  exact placed_valid 7 (7, 8) valid_381

theorem eq_inline_474 : inline_474 = combine (5, 7) [placed 0 (5, 4) card_64, placed 5 (2, 8) card_500] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_474 : Valid inline_474 := by
  rw [eq_inline_474]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 4) valid_64
  subst c
  exact placed_valid 5 (2, 8) valid_500

theorem eq_inline_475 : inline_475 = combine (5, 5) [inline_472, inline_473, inline_474, placed 5 (1, 8) card_601] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_475 : Valid inline_475 := by
  rw [eq_inline_475]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_472
  rcases hc with rfl | hc
  · exact valid_inline_473
  rcases hc with rfl | hc
  · exact valid_inline_474
  subst c
  exact placed_valid 5 (1, 8) valid_601

theorem eq_inline_476 : inline_476 = combine (6, 8) [placed 0 (3, 5) card_119, placed 5 (2, 8) card_497, placed 1 (2, 4) card_498, inline_475] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_476 : Valid inline_476 := by
  rw [eq_inline_476]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 5) valid_119
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_497
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_498
  subst c
  exact valid_inline_475

theorem eq_card_602 : card_602 = combine (6, 7) [placed 0 (0, 1) card_553, inline_469, inline_471, placed 0 (2, 2) card_557, placed 1 (2, 4) card_564, placed 1 (2, 4) card_568, placed 5 (0, 8) card_573, placed 2 (2, 10) card_574, placed 2 (0, 13) card_583, placed 2 (0, 12) card_598, placed 0 (3, 4) card_599, inline_476] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_602 : Valid card_602 := by
  rw [eq_card_602]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_553
  rcases hc with rfl | hc
  · exact valid_inline_469
  rcases hc with rfl | hc
  · exact valid_inline_471
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_557
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_564
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_568
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 8) valid_573
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_574
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 13) valid_583
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 12) valid_598
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_599
  subst c
  exact valid_inline_476

theorem eq_inline_477 : inline_477 = combine (1, 2) [placed 2 (1, 6) card_7, placed 5 (0, 5) card_8, placed 6 (2, 6) card_9, placed 2 (0, 6) card_427] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_477 : Valid inline_477 := by
  rw [eq_inline_477]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_9
  subst c
  exact placed_valid 2 (0, 6) valid_427

theorem eq_card_603 : card_603 = combine (1, 5) [placed 4 (2, 1) card_13, placed 6 (2, 7) card_14, placed 2 (0, 7) card_31, placed 4 (2, 1) card_189, placed 2 (0, 7) card_367, placed 0 (0, 2) card_457, inline_477] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_603 : Valid card_603 := by
  rw [eq_card_603]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_367
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_457
  subst c
  exact valid_inline_477


end OAI.Snaky21.Certificate

theorem solution : Valid card_600 ∧ Valid card_601 ∧ Valid card_602 ∧ Valid card_603 ∧ True :=
  ⟨valid_600, valid_601, valid_602, valid_603, True.intro⟩
