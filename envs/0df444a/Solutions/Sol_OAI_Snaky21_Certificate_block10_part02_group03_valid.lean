-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part02_group03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:34:57.479098+00:00
-- url     : https://prove2.me/submissions/2194d3be-0fac-4ff4-bf8d-4cc2931b59ec

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part02_group00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part02_group02_valid
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
theorem valid_4 : Valid card_4 := block00_valid.2.2.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_43 : Valid card_43 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_50 : Valid card_50 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_57 : Valid card_57 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_67 : Valid card_67 := block01_valid.2.2.2.1
theorem valid_96 : Valid card_96 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_97 : Valid card_97 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_98 : Valid card_98 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_115 : Valid card_115 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_118 : Valid card_118 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_134 : Valid card_134 := block02_valid.2.2.2.2.2.2.1
theorem valid_174 : Valid card_174 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_175 : Valid card_175 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_180 : Valid card_180 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_228 : Valid card_228 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_256 : Valid card_256 := block04_valid.1
theorem valid_257 : Valid card_257 := block04_valid.2.1
theorem valid_312 : Valid card_312 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_313 : Valid card_313 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_324 : Valid card_324 := block05_valid.2.2.2.2.1
theorem valid_337 : Valid card_337 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_340 : Valid card_340 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_351 : Valid card_351 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_355 : Valid card_355 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_434 : Valid card_434 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_454 : Valid card_454 := block07_valid.2.2.2.2.2.2.1
theorem valid_455 : Valid card_455 := block07_valid.2.2.2.2.2.2.2.1
theorem valid_468 : Valid card_468 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_469 : Valid card_469 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_470 : Valid card_470 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_475 : Valid card_475 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_483 : Valid card_483 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_485 : Valid card_485 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_489 : Valid card_489 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_491 : Valid card_491 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_508 : Valid card_508 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_531 : Valid card_531 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_558 : Valid card_558 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_566 : Valid card_566 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_587 : Valid card_587 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_623 : Valid card_623 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_624 : Valid card_624 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_625 : Valid card_625 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_630 : Valid card_630 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_632 : Valid card_632 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_635 : Valid card_635 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_636 : Valid card_636 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_639 : Valid card_639 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_644 : Valid card_644 := block10_part00_valid.2.2.2.2.1
theorem valid_645 : Valid card_645 := block10_part00_valid.2.2.2.2.2.1
theorem valid_647 : Valid card_647 := block10_part00_valid.2.2.2.2.2.2.2.1
theorem valid_656 : Valid card_656 := block10_part01_valid.1
theorem valid_657 : Valid card_657 := block10_part01_valid.2.1
theorem valid_670 : Valid card_670 := block10_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_675 : Valid card_675 := block10_part02_group00_valid.2.2.2.1
theorem valid_683 : Valid card_683 := block10_part02_group02_valid.2.2.2.1

theorem eq_inline_706 : inline_706 = combine (9, 7) [placed 2 (6, 8) card_8, placed 2 (6, 10) card_115, placed 1 (5, 6) card_469, placed 2 (5, 12) card_470, placed 5 (4, 8) card_485, placed 2 (4, 12) card_489] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_706 : Valid inline_706 := by
  rw [eq_inline_706]
  apply combination_rule (9, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 8) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 10) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 6) valid_469
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 12) valid_470
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_485
  subst c
  exact placed_valid 2 (4, 12) valid_489

theorem eq_inline_707 : inline_707 = combine (8, 7) [placed 2 (5, 10) card_118, placed 5 (5, 10) card_355, placed 5 (5, 11) card_434, placed 1 (3, 6) card_468, inline_706, placed 7 (9, 11) card_491] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_707 : Valid inline_707 := by
  rw [eq_inline_707]
  apply combination_rule (8, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 10) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 10) valid_355
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 11) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_468
  rcases hc with rfl | hc
  · exact valid_inline_706
  subst c
  exact placed_valid 7 (9, 11) valid_491

theorem eq_inline_708 : inline_708 = combine (7, 9) [placed 0 (6, 6) card_50, placed 0 (6, 6) card_97, placed 4 (7, 6) card_98, placed 6 (8, 11) card_454, placed 3 (8, 7) card_455, placed 1 (2, 6) card_624] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_708 : Valid inline_708 := by
  rw [eq_inline_708]
  apply combination_rule (7, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 6) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 6) valid_97
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 6) valid_98
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 11) valid_454
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 7) valid_455
  subst c
  exact placed_valid 1 (2, 6) valid_624

theorem eq_inline_709 : inline_709 = combine (7, 11) [placed 2 (4, 14) card_174, placed 0 (5, 7) card_475, placed 4 (9, 7) card_475, placed 0 (5, 7) card_483, placed 1 (4, 8) card_508, placed 3 (10, 8) card_508, placed 2 (4, 14) card_566, placed 0 (5, 7) card_587, placed 4 (9, 7) card_587, placed 2 (5, 15) card_635, placed 2 (3, 15) card_644, placed 2 (3, 15) card_645, placed 2 (3, 15) card_647] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_709 : Valid inline_709 := by
  rw [eq_inline_709]
  apply combination_rule (7, 11) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 14) valid_174
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 7) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 7) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 7) valid_483
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 8) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 8) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 14) valid_566
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 7) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 7) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 15) valid_635
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 15) valid_644
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 15) valid_645
  subst c
  exact placed_valid 2 (3, 15) valid_647

theorem eq_inline_710 : inline_710 = combine (9, 7) [placed 0 (6, 6) card_8, placed 4 (9, 6) card_313] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_710 : Valid inline_710 := by
  rw [eq_inline_710]
  apply combination_rule (9, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 6) valid_8
  subst c
  exact placed_valid 4 (9, 6) valid_313

theorem eq_inline_711 : inline_711 = combine (8, 7) [placed 0 (5, 4) card_257, inline_710, placed 5 (5, 11) card_434, placed 3 (11, 6) card_468, placed 7 (9, 11) card_491] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_711 : Valid inline_711 := by
  rw [eq_inline_711]
  apply combination_rule (8, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 4) valid_257
  rcases hc with rfl | hc
  · exact valid_inline_710
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 11) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 6) valid_468
  subst c
  exact placed_valid 7 (9, 11) valid_491

theorem eq_card_684 : card_684 = combine (7, 10) [inline_707, placed 5 (0, 15) card_623, inline_708, placed 3 (9, 6) card_625, placed 5 (0, 14) card_630, placed 3 (10, 6) card_632, placed 3 (11, 6) card_636, placed 1 (3, 6) card_639, inline_709, placed 1 (1, 5) card_656, placed 1 (4, 5) card_657, placed 1 (2, 4) card_670, placed 3 (12, 3) card_675, placed 1 (2, 6) card_683, inline_711] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_684 : Valid card_684 := by
  rw [eq_card_684]
  apply combination_rule (7, 10) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_707
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 15) valid_623
  rcases hc with rfl | hc
  · exact valid_inline_708
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 6) valid_625
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 14) valid_630
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 6) valid_632
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 6) valid_636
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_639
  rcases hc with rfl | hc
  · exact valid_inline_709
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 5) valid_656
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 5) valid_657
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_670
  rcases hc with rfl | hc
  · exact placed_valid 3 (12, 3) valid_675
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 6) valid_683
  subst c
  exact valid_inline_711

theorem eq_inline_712 : inline_712 = combine (3, 1) [placed 7 (3, 4) card_5, placed 0 (2, 0) card_312] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_712 : Valid inline_712 := by
  rw [eq_inline_712]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_312

theorem eq_inline_713 : inline_713 = combine (2, 1) [placed 7 (3, 5) card_4, inline_712] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_713 : Valid inline_713 := by
  rw [eq_inline_713]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 5) valid_4
  subst c
  exact valid_inline_712

theorem eq_inline_714 : inline_714 = combine (6, 2) [placed 2 (3, 6) card_351, inline_713] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_714 : Valid inline_714 := by
  rw [eq_inline_714]
  apply combination_rule (6, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_351
  subst c
  exact valid_inline_713

theorem eq_inline_715 : inline_715 = combine (6, 4) [placed 1 (2, 2) card_96, inline_714] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_715 : Valid inline_715 := by
  rw [eq_inline_715]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_96
  subst c
  exact valid_inline_714

theorem eq_inline_716 : inline_716 = combine (3, 2) [placed 1 (3, 2) card_5, inline_715] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_716 : Valid inline_716 := by
  rw [eq_inline_716]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 2) valid_5
  subst c
  exact valid_inline_715

theorem eq_card_685 : card_685 = combine (5, 5) [placed 5 (1, 6) card_67, placed 7 (7, 6) card_175, placed 0 (2, 2) card_228, placed 2 (2, 8) card_435, placed 0 (3, 2) card_531, inline_716] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_685 : Valid card_685 := by
  rw [eq_card_685]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_175
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_228
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_531
  subst c
  exact valid_inline_716

theorem eq_inline_717 : inline_717 = combine (5, 4) [placed 1 (2, 3) card_43, placed 3 (7, 2) card_57, placed 0 (3, 0) card_340] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_717 : Valid inline_717 := by
  rw [eq_inline_717]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_43
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 2) valid_57
  subst c
  exact placed_valid 0 (3, 0) valid_340

theorem eq_inline_718 : inline_718 = combine (4, 2) [placed 2 (4, 6) card_7, placed 2 (3, 6) card_9, placed 3 (7, 2) card_256] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_718 : Valid inline_718 := by
  rw [eq_inline_718]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_9
  subst c
  exact placed_valid 3 (7, 2) valid_256

theorem eq_card_686 : card_686 = combine (4, 5) [placed 3 (6, 2) card_134, placed 3 (6, 2) card_180, placed 0 (3, 0) card_337, placed 3 (7, 2) card_435, placed 3 (6, 3) card_558, inline_717, inline_718] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_686 : Valid card_686 := by
  rw [eq_card_686]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_337
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 2) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_558
  rcases hc with rfl | hc
  · exact valid_inline_717
  subst c
  exact valid_inline_718

theorem eq_card_687 : card_687 = combine (5, 5) [placed 1 (2, 4) card_44, placed 4 (6, 0) card_324, placed 1 (0, 1) card_685, placed 0 (1, 1) card_686] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_687 : Valid card_687 := by
  rw [eq_card_687]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 0) valid_324
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_685
  subst c
  exact placed_valid 0 (1, 1) valid_686


end OAI.Snaky21.Certificate

theorem solution : Valid card_684 ∧ Valid card_685 ∧ Valid card_686 ∧ Valid card_687 ∧ True :=
  ⟨valid_684, valid_685, valid_686, valid_687, True.intro⟩
