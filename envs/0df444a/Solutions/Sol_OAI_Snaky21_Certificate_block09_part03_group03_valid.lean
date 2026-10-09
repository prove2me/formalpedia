-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part03_group03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:55:04.315332+00:00
-- url     : https://prove2.me/submissions/5d4d44a6-d4fb-4b4c-8723-d5191952aa40

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part03_group02_valid
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
theorem valid_1 : Valid card_1 := block00_valid.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_21 : Valid card_21 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_37 : Valid card_37 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_41 : Valid card_41 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_48 : Valid card_48 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_50 : Valid card_50 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_54 : Valid card_54 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_57 : Valid card_57 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_62 : Valid card_62 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_63 : Valid card_63 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_71 : Valid card_71 := block01_valid.2.2.2.2.2.2.2.1
theorem valid_73 : Valid card_73 := block01_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_85 : Valid card_85 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_108 : Valid card_108 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_117 : Valid card_117 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_118 : Valid card_118 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_125 : Valid card_125 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_136 : Valid card_136 := block02_valid.2.2.2.2.2.2.2.2.1
theorem valid_164 : Valid card_164 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_188 : Valid card_188 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_192 : Valid card_192 := block03_valid.1
theorem valid_193 : Valid card_193 := block03_valid.2.1
theorem valid_217 : Valid card_217 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_262 : Valid card_262 := block04_valid.2.2.2.2.2.2.1
theorem valid_331 : Valid card_331 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_332 : Valid card_332 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_396 : Valid card_396 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_399 : Valid card_399 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_408 : Valid card_408 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_451 : Valid card_451 := block07_valid.2.2.2.1
theorem valid_454 : Valid card_454 := block07_valid.2.2.2.2.2.2.1
theorem valid_474 : Valid card_474 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_475 : Valid card_475 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_478 : Valid card_478 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_482 : Valid card_482 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_509 : Valid card_509 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_512 : Valid card_512 := block08_valid.1
theorem valid_522 : Valid card_522 := block08_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_530 : Valid card_530 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_587 : Valid card_587 := block09_part00_valid.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_635 : Valid card_635 := block09_part03_group02_valid.2.2.2.1

theorem eq_inline_572 : inline_572 = combine (3, 5) [placed 7 (5, 5) card_22, placed 6 (5, 7) card_108, placed 0 (2, 1) card_512] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_572 : Valid inline_572 := by
  rw [eq_inline_572]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_108
  subst c
  exact placed_valid 0 (2, 1) valid_512

theorem eq_inline_573 : inline_573 = combine (4, 6) [placed 0 (3, 3) card_10, placed 6 (4, 7) card_44, placed 0 (3, 3) card_63, placed 5 (1, 7) card_117] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_573 : Valid inline_573 := by
  rw [eq_inline_573]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_63
  subst c
  exact placed_valid 5 (1, 7) valid_117

theorem eq_inline_574 : inline_574 = combine (5, 5) [placed 0 (3, 1) card_85, placed 0 (3, 2) card_164, placed 2 (2, 7) card_262] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_574 : Valid inline_574 := by
  rw [eq_inline_574]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_85
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_164
  subst c
  exact placed_valid 2 (2, 7) valid_262

theorem eq_inline_575 : inline_575 = combine (3, 5) [placed 2 (1, 5) card_1, inline_574] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_575 : Valid inline_575 := by
  rw [eq_inline_575]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_1
  subst c
  exact valid_inline_574

theorem eq_inline_576 : inline_576 = combine (6, 4) [placed 5 (2, 4) card_7, placed 1 (2, 4) card_11, placed 4 (6, 1) card_331] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_576 : Valid inline_576 := by
  rw [eq_inline_576]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_11
  subst c
  exact placed_valid 4 (6, 1) valid_331

theorem eq_inline_577 : inline_577 = combine (5, 4) [placed 0 (2, 1) card_332, placed 2 (2, 6) card_474, placed 0 (2, 2) card_522, inline_575, inline_576] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_577 : Valid inline_577 := by
  rw [eq_inline_577]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_332
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_474
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_522
  rcases hc with rfl | hc
  · exact valid_inline_575
  subst c
  exact valid_inline_576

theorem eq_inline_578 : inline_578 = combine (4, 5) [placed 2 (2, 8) card_399, placed 0 (3, 1) card_408, placed 2 (2, 8) card_475, placed 1 (1, 2) card_509, placed 0 (2, 1) card_587, inline_572, placed 2 (2, 9) card_635, inline_573, inline_577] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_578 : Valid inline_578 := by
  rw [eq_inline_578]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_399
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_408
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_509
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_587
  rcases hc with rfl | hc
  · exact valid_inline_572
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_635
  rcases hc with rfl | hc
  · exact valid_inline_573
  subst c
  exact valid_inline_577

theorem eq_inline_579 : inline_579 = combine (5, 4) [placed 0 (2, 1) card_118, placed 1 (1, 2) card_188, placed 5 (1, 6) card_188, placed 1 (1, 3) card_192, placed 1 (1, 3) card_193, placed 3 (8, 2) card_396] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_579 : Valid inline_579 := by
  rw [eq_inline_579]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_193
  subst c
  exact placed_valid 3 (8, 2) valid_396

theorem eq_card_636 : card_636 = combine (3, 4) [placed 5 (0, 5) card_125, placed 3 (5, 3) card_454, inline_578, inline_579] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_636 : Valid card_636 := by
  rw [eq_card_636]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_454
  rcases hc with rfl | hc
  · exact valid_inline_578
  subst c
  exact valid_inline_579

theorem eq_inline_580 : inline_580 = combine (4, 4) [placed 6 (4, 5) card_15, placed 1 (1, 3) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_580 : Valid inline_580 := by
  rw [eq_inline_580]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_15
  subst c
  exact placed_valid 1 (1, 3) valid_44

theorem eq_inline_581 : inline_581 = combine (3, 3) [placed 0 (0, 2) card_0, inline_580] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_581 : Valid inline_581 := by
  rw [eq_inline_581]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_0
  subst c
  exact valid_inline_580

theorem eq_inline_582 : inline_582 = combine (4, 3) [placed 0 (1, 2) card_5, inline_581] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_582 : Valid inline_582 := by
  rw [eq_inline_582]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_5
  subst c
  exact valid_inline_581

theorem eq_card_637 : card_637 = combine (4, 2) [placed 1 (1, 2) card_21, placed 5 (1, 3) card_41, placed 5 (1, 3) card_48, inline_582] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_637 : Valid card_637 := by
  rw [eq_card_637]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 3) valid_41
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 3) valid_48
  subst c
  exact valid_inline_582

theorem eq_inline_583 : inline_583 = combine (3, 4) [placed 1 (0, 3) card_15, placed 2 (1, 7) card_85] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_583 : Valid inline_583 := by
  rw [eq_inline_583]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_15
  subst c
  exact placed_valid 2 (1, 7) valid_85

theorem eq_card_638 : card_638 = combine (3, 3) [placed 2 (0, 6) card_57, placed 5 (0, 5) card_136, placed 5 (0, 5) card_217, placed 0 (1, 0) card_530, inline_583, placed 0 (0, 1) card_637] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_638 : Valid card_638 := by
  rw [eq_card_638]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_136
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_217
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_530
  rcases hc with rfl | hc
  · exact valid_inline_583
  subst c
  exact placed_valid 0 (0, 1) valid_637

theorem eq_inline_584 : inline_584 = combine (3, 6) [placed 0 (3, 3) card_21, placed 4 (4, 3) card_37, placed 6 (4, 7) card_62] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_584 : Valid inline_584 := by
  rw [eq_inline_584]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_37
  subst c
  exact placed_valid 6 (4, 7) valid_62

theorem eq_inline_585 : inline_585 = combine (3, 5) [placed 4 (4, 2) card_71, placed 6 (4, 6) card_73, inline_584, placed 6 (4, 6) card_451] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_585 : Valid inline_585 := by
  rw [eq_inline_585]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_73
  rcases hc with rfl | hc
  · exact valid_inline_584
  subst c
  exact placed_valid 6 (4, 6) valid_451

theorem eq_inline_586 : inline_586 = combine (3, 5) [placed 4 (4, 2) card_71, placed 6 (4, 6) card_73, placed 3 (6, 2) card_435, placed 6 (4, 6) card_451] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_586 : Valid inline_586 := by
  rw [eq_inline_586]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_73
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_435
  subst c
  exact placed_valid 6 (4, 6) valid_451

theorem eq_inline_587 : inline_587 = combine (3, 3) [placed 1 (0, 3) card_54, placed 1 (0, 2) card_638, inline_585, inline_586] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_587 : Valid inline_587 := by
  rw [eq_inline_587]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_638
  rcases hc with rfl | hc
  · exact valid_inline_585
  subst c
  exact valid_inline_586

theorem eq_card_639 : card_639 = combine (3, 4) [placed 1 (0, 3) card_50, placed 1 (0, 3) card_125, placed 0 (0, 2) card_478, placed 0 (0, 2) card_482, inline_587] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_639 : Valid card_639 := by
  rw [eq_card_639]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_478
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_482
  subst c
  exact valid_inline_587


end OAI.Snaky21.Certificate

theorem solution : Valid card_636 ∧ Valid card_637 ∧ Valid card_638 ∧ Valid card_639 ∧ True :=
  ⟨valid_636, valid_637, valid_638, valid_639, True.intro⟩
