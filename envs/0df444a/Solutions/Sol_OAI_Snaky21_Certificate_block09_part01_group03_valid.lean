-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part01_group03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:34:02.052016+00:00
-- url     : https://prove2.me/submissions/e99d77b1-2274-431b-b397-b762b4fdf62a

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_group02_valid
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
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_25 : Valid card_25 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_28 : Valid card_28 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_42 : Valid card_42 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_115 : Valid card_115 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_135 : Valid card_135 := block02_valid.2.2.2.2.2.2.2.1
theorem valid_168 : Valid card_168 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_182 : Valid card_182 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_197 : Valid card_197 := block03_valid.2.2.2.2.2.1
theorem valid_211 : Valid card_211 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_240 : Valid card_240 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_267 : Valid card_267 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_352 : Valid card_352 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_363 : Valid card_363 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_371 : Valid card_371 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_383 : Valid card_383 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_474 : Valid card_474 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_585 : Valid card_585 := block09_part00_valid.2.2.2.2.2.2.2.2.2.1


theorem eq_inline_478 : inline_478 = combine (3, 4) [placed 0 (0, 3) card_5, placed 0 (1, 0) card_267] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_478 : Valid inline_478 := by
  rw [eq_inline_478]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_267

theorem eq_card_604 : card_604 = combine (3, 2) [placed 2 (0, 3) card_5, inline_478] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_604 : Valid card_604 := by
  rw [eq_card_604]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact valid_inline_478

theorem eq_inline_479 : inline_479 = combine (1, 3) [placed 4 (4, 0) card_115, placed 0 (0, 1) card_585, placed 0 (1, 0) card_604] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_479 : Valid inline_479 := by
  rw [eq_inline_479]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_585
  subst c
  exact placed_valid 0 (1, 0) valid_604

theorem eq_card_605 : card_605 = combine (4, 3) [placed 1 (0, 2) card_12, placed 1 (0, 1) card_135, placed 5 (0, 5) card_182, placed 0 (1, 1) card_474, inline_479] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_605 : Valid card_605 := by
  rw [eq_card_605]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_182
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_474
  subst c
  exact valid_inline_479

theorem eq_inline_480 : inline_480 = combine (3, 4) [placed 2 (3, 6) card_53, placed 4 (4, 1) card_240] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_480 : Valid inline_480 := by
  rw [eq_inline_480]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_53
  subst c
  exact placed_valid 4 (4, 1) valid_240

theorem eq_card_606 : card_606 = combine (3, 3) [placed 1 (0, 2) card_28, placed 0 (0, 1) card_168, inline_480] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_606 : Valid card_606 := by
  rw [eq_card_606]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_168
  subst c
  exact valid_inline_480

theorem eq_inline_481 : inline_481 = combine (4, 2) [placed 5 (3, 5) card_8, placed 3 (6, 2) card_383] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_481 : Valid inline_481 := by
  rw [eq_inline_481]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_8
  subst c
  exact placed_valid 3 (6, 2) valid_383

theorem eq_inline_482 : inline_482 = combine (2, 5) [placed 3 (5, 3) card_25, placed 6 (2, 6) card_42] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_482 : Valid inline_482 := by
  rw [eq_inline_482]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_25
  subst c
  exact placed_valid 6 (2, 6) valid_42

theorem eq_inline_483 : inline_483 = combine (1, 2) [placed 7 (5, 6) card_352, inline_482] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_483 : Valid inline_483 := by
  rw [eq_inline_483]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_352
  subst c
  exact valid_inline_482

theorem eq_inline_484 : inline_484 = combine (4, 6) [placed 6 (4, 7) card_7, placed 3 (5, 3) card_8, inline_483] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_484 : Valid inline_484 := by
  rw [eq_inline_484]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_8
  subst c
  exact valid_inline_483

theorem eq_inline_485 : inline_485 = combine (4, 6) [placed 3 (5, 3) card_197, placed 0 (1, 2) card_363, placed 3 (5, 3) card_371, placed 4 (5, 2) card_606] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_485 : Valid inline_485 := by
  rw [eq_inline_485]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_363
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_371
  subst c
  exact placed_valid 4 (5, 2) valid_606

theorem eq_card_607 : card_607 = combine (4, 3) [placed 6 (5, 7) card_13, placed 2 (1, 7) card_211, inline_481, inline_484, inline_485] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_607 : Valid card_607 := by
  rw [eq_card_607]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_211
  rcases hc with rfl | hc
  · exact valid_inline_481
  rcases hc with rfl | hc
  · exact valid_inline_484
  subst c
  exact valid_inline_485


end OAI.Snaky21.Certificate

theorem solution : Valid card_604 ∧ Valid card_605 ∧ Valid card_606 ∧ Valid card_607 ∧ True :=
  ⟨valid_604, valid_605, valid_606, valid_607, True.intro⟩
