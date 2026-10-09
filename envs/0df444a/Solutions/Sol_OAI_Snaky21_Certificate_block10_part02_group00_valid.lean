-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part02_group00_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:32:48.817082+00:00
-- url     : https://prove2.me/submissions/c0faa80b-e779-452e-9adb-99e75a1ec8ab

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
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_19 : Valid card_19 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_25 : Valid card_25 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_26 : Valid card_26 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_30 : Valid card_30 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_34 : Valid card_34 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_38 : Valid card_38 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_74 : Valid card_74 := block01_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_97 : Valid card_97 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_133 : Valid card_133 := block02_valid.2.2.2.2.2.1
theorem valid_145 : Valid card_145 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_149 : Valid card_149 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_179 : Valid card_179 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_186 : Valid card_186 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_187 : Valid card_187 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_188 : Valid card_188 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_190 : Valid card_190 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_230 : Valid card_230 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_260 : Valid card_260 := block04_valid.2.2.2.2.1
theorem valid_263 : Valid card_263 := block04_valid.2.2.2.2.2.2.2.1
theorem valid_271 : Valid card_271 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_304 : Valid card_304 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_305 : Valid card_305 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_306 : Valid card_306 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_321 : Valid card_321 := block05_valid.2.1
theorem valid_328 : Valid card_328 := block05_valid.2.2.2.2.2.2.2.2.1
theorem valid_330 : Valid card_330 := block05_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_354 : Valid card_354 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_356 : Valid card_356 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_363 : Valid card_363 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_364 : Valid card_364 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_367 : Valid card_367 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_384 : Valid card_384 := block06_valid.1
theorem valid_424 : Valid card_424 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_441 : Valid card_441 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_442 : Valid card_442 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_459 : Valid card_459 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_514 : Valid card_514 := block08_valid.2.2.1
theorem valid_535 : Valid card_535 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_618 : Valid card_618 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_629 : Valid card_629 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_667 : Valid card_667 := block10_part01_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_671 : Valid card_671 := block10_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem eq_inline_664 : inline_664 = combine (2, 1) [placed 0 (1, 0) card_22, placed 1 (0, 1) card_22] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_664 : Valid inline_664 := by
  rw [eq_inline_664]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_22
  subst c
  exact placed_valid 1 (0, 1) valid_22

theorem eq_card_672 : card_672 = combine (2, 2) [placed 5 (0, 2) card_34, placed 1 (0, 1) card_305, inline_664] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_672 : Valid card_672 := by
  rw [eq_card_672]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_34
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_305
  subst c
  exact valid_inline_664

theorem eq_inline_665 : inline_665 = combine (1, 4) [placed 0 (1, 3) card_30, placed 5 (1, 4) card_74] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_665 : Valid inline_665 := by
  rw [eq_inline_665]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_30
  subst c
  exact placed_valid 5 (1, 4) valid_74

theorem eq_inline_666 : inline_666 = combine (4, 5) [placed 0 (1, 4) card_5, placed 0 (1, 3) card_260] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_666 : Valid inline_666 := by
  rw [eq_inline_666]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_5
  subst c
  exact placed_valid 0 (1, 3) valid_260

theorem eq_inline_667 : inline_667 = combine (1, 4) [placed 4 (4, 3) card_38, inline_666] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_667 : Valid inline_667 := by
  rw [eq_inline_667]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_38
  subst c
  exact valid_inline_666

theorem eq_inline_668 : inline_668 = combine (3, 4) [placed 6 (5, 4) card_0, inline_667] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_668 : Valid inline_668 := by
  rw [eq_inline_668]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact valid_inline_667

theorem eq_inline_669 : inline_669 = combine (4, 5) [placed 0 (2, 2) card_188, placed 6 (6, 8) card_190, placed 7 (6, 7) card_230, placed 0 (1, 3) card_263, placed 2 (1, 8) card_306] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_669 : Valid inline_669 := by
  rw [eq_inline_669]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_230
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_263
  subst c
  exact placed_valid 2 (1, 8) valid_306

theorem eq_inline_670 : inline_670 = combine (1, 4) [placed 4 (4, 3) card_38, placed 0 (1, 3) card_145] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_670 : Valid inline_670 := by
  rw [eq_inline_670]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_38
  subst c
  exact placed_valid 0 (1, 3) valid_145

theorem eq_inline_671 : inline_671 = combine (3, 4) [placed 6 (5, 4) card_0, inline_670] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_671 : Valid inline_671 := by
  rw [eq_inline_671]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact valid_inline_670

theorem eq_inline_672 : inline_672 = combine (4, 3) [placed 5 (3, 6) card_8, placed 0 (3, 2) card_19, placed 7 (5, 6) card_25] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_672 : Valid inline_672 := by
  rw [eq_inline_672]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_19
  subst c
  exact placed_valid 7 (5, 6) valid_25

theorem eq_inline_673 : inline_673 = combine (3, 4) [placed 0 (1, 4) card_5, placed 0 (3, 3) card_10] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_673 : Valid inline_673 := by
  rw [eq_inline_673]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_5
  subst c
  exact placed_valid 0 (3, 3) valid_10

theorem eq_inline_674 : inline_674 = combine (4, 5) [placed 2 (1, 7) card_263, placed 2 (1, 7) card_271, placed 2 (1, 7) card_424, inline_672, inline_673] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_674 : Valid inline_674 := by
  rw [eq_inline_674]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_263
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_271
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_424
  rcases hc with rfl | hc
  · exact valid_inline_672
  subst c
  exact valid_inline_673

theorem eq_inline_675 : inline_675 = combine (1, 4) [placed 0 (1, 3) card_30, inline_674] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_675 : Valid inline_675 := by
  rw [eq_inline_675]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_30
  subst c
  exact valid_inline_674

theorem eq_card_673 : card_673 = combine (4, 4) [inline_665, inline_668, inline_669, inline_671, inline_675] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_673 : Valid card_673 := by
  rw [eq_card_673]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_665
  rcases hc with rfl | hc
  · exact valid_inline_668
  rcases hc with rfl | hc
  · exact valid_inline_669
  rcases hc with rfl | hc
  · exact valid_inline_671
  subst c
  exact valid_inline_675

theorem eq_card_674 : card_674 = combine (2, 4) [placed 4 (2, 2) card_34, placed 0 (1, 2) card_149, placed 0 (0, 0) card_673] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_674 : Valid card_674 := by
  rw [eq_card_674]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_34
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_149
  subst c
  exact placed_valid 0 (0, 0) valid_673

theorem eq_inline_676 : inline_676 = combine (7, 7) [placed 4 (8, 3) card_12, placed 0 (4, 3) card_356, placed 0 (4, 3) card_364, placed 4 (8, 3) card_367, placed 6 (8, 9) card_671] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_676 : Valid inline_676 := by
  rw [eq_inline_676]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_356
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_364
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_367
  subst c
  exact placed_valid 6 (8, 9) valid_671

theorem eq_inline_677 : inline_677 = combine (7, 4) [placed 0 (5, 2) card_188, placed 6 (9, 8) card_190, placed 4 (8, 2) card_441, placed 4 (8, 2) card_442, placed 6 (8, 7) card_514, placed 0 (4, 3) card_667] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_677 : Valid inline_677 := by
  rw [eq_inline_677]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 8) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 2) valid_441
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 2) valid_442
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 7) valid_514
  subst c
  exact placed_valid 0 (4, 3) valid_667

theorem eq_inline_678 : inline_678 = combine (7, 4) [placed 5 (6, 6) card_8, placed 7 (8, 6) card_26, placed 1 (5, 2) card_133, placed 0 (6, 1) card_186, placed 2 (7, 8) card_187] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_678 : Valid inline_678 := by
  rw [eq_inline_678]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (6, 6) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 2) valid_133
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 1) valid_186
  subst c
  exact placed_valid 2 (7, 8) valid_187

theorem eq_inline_679 : inline_679 = combine (7, 4) [placed 3 (7, 3) card_5, placed 3 (9, 2) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_679 : Valid inline_679 := by
  rw [eq_inline_679]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_5
  subst c
  exact placed_valid 3 (9, 2) valid_179

theorem eq_inline_680 : inline_680 = combine (6, 5) [placed 7 (8, 6) card_22, placed 3 (8, 5) card_34, placed 7 (8, 6) card_305] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_680 : Valid inline_680 := by
  rw [eq_inline_680]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_34
  subst c
  exact placed_valid 7 (8, 6) valid_305

theorem eq_inline_681 : inline_681 = combine (6, 6) [inline_679, inline_680] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_681 : Valid inline_681 := by
  rw [eq_inline_681]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_679
  subst c
  exact valid_inline_680

theorem eq_inline_682 : inline_682 = combine (7, 3) [placed 2 (6, 8) card_304, placed 6 (8, 7) card_672, inline_678, placed 5 (1, 7) card_674, inline_681] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_682 : Valid inline_682 := by
  rw [eq_inline_682]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 8) valid_304
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 7) valid_672
  rcases hc with rfl | hc
  · exact valid_inline_678
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_674
  subst c
  exact valid_inline_681

theorem eq_inline_683 : inline_683 = combine (7, 7) [placed 0 (5, 3) card_190, placed 4 (9, 3) card_190, placed 0 (4, 3) card_363, placed 6 (8, 9) card_671] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_683 : Valid inline_683 := by
  rw [eq_inline_683]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 3) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_363
  subst c
  exact placed_valid 6 (8, 9) valid_671

theorem eq_inline_684 : inline_684 = combine (6, 5) [placed 3 (8, 5) card_34, placed 5 (3, 6) card_97, placed 2 (5, 10) card_535] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_684 : Valid inline_684 := by
  rw [eq_inline_684]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_34
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_97
  subst c
  exact placed_valid 2 (5, 10) valid_535

theorem eq_inline_685 : inline_685 = combine (7, 4) [placed 5 (3, 6) card_321, placed 3 (8, 3) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_685 : Valid inline_685 := by
  rw [eq_inline_685]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_321
  subst c
  exact placed_valid 3 (8, 3) valid_354

theorem eq_inline_686 : inline_686 = combine (7, 3) [placed 5 (3, 7) card_328, placed 5 (3, 7) card_330, placed 2 (4, 7) card_384, placed 6 (8, 7) card_672, placed 5 (1, 7) card_674, inline_685] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_686 : Valid inline_686 := by
  rw [eq_inline_686]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_328
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_330
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_384
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 7) valid_672
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_674
  subst c
  exact valid_inline_685

theorem eq_card_675 : card_675 = combine (7, 6) [placed 0 (6, 1) card_459, placed 0 (2, 2) card_618, placed 4 (10, 2) card_629, inline_676, inline_677, inline_682, inline_683, inline_684, inline_686] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_675 : Valid card_675 := by
  rw [eq_card_675]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 1) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_618
  rcases hc with rfl | hc
  · exact placed_valid 4 (10, 2) valid_629
  rcases hc with rfl | hc
  · exact valid_inline_676
  rcases hc with rfl | hc
  · exact valid_inline_677
  rcases hc with rfl | hc
  · exact valid_inline_682
  rcases hc with rfl | hc
  · exact valid_inline_683
  rcases hc with rfl | hc
  · exact valid_inline_684
  subst c
  exact valid_inline_686


end OAI.Snaky21.Certificate

theorem solution : Valid card_672 ∧ Valid card_673 ∧ Valid card_674 ∧ Valid card_675 ∧ True :=
  ⟨valid_672, valid_673, valid_674, valid_675, True.intro⟩
