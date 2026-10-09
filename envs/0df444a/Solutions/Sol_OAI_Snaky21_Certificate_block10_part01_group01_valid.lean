-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part01_group01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:30:52.491891+00:00
-- url     : https://prove2.me/submissions/302c0df0-6c94-47f7-adcf-73cd32ab1f2b

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_group00_valid
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
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_18 : Valid card_18 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_33 : Valid card_33 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_115 : Valid card_115 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_116 : Valid card_116 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_134 : Valid card_134 := block02_valid.2.2.2.2.2.2.1
theorem valid_137 : Valid card_137 := block02_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_141 : Valid card_141 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_180 : Valid card_180 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_252 : Valid card_252 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_302 : Valid card_302 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_303 : Valid card_303 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_332 : Valid card_332 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_507 : Valid card_507 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_558 : Valid card_558 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_562 : Valid card_562 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_580 : Valid card_580 := block09_valid.2.2.2.2.1

theorem valid_658 : Valid card_658 := block10_part01_group00_valid.2.2.1
theorem valid_659 : Valid card_659 := block10_part01_group00_valid.2.2.2.1

theorem eq_inline_632 : inline_632 = combine (7, 5) [placed 3 (7, 5) card_6, placed 1 (4, 4) card_18] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_632 : Valid inline_632 := by
  rw [eq_inline_632]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_6
  subst c
  exact placed_valid 1 (4, 4) valid_18

theorem eq_inline_633 : inline_633 = combine (7, 5) [placed 3 (7, 5) card_6, placed 0 (3, 2) card_252] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_633 : Valid inline_633 := by
  rw [eq_inline_633]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_6
  subst c
  exact placed_valid 0 (3, 2) valid_252

theorem eq_inline_634 : inline_634 = combine (6, 5) [placed 5 (2, 6) card_9, inline_632, placed 0 (3, 0) card_659, inline_633] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_634 : Valid inline_634 := by
  rw [eq_inline_634]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 6) valid_9
  rcases hc with rfl | hc
  · exact valid_inline_632
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_659
  subst c
  exact valid_inline_633

theorem eq_card_660 : card_660 = combine (3, 5) [placed 3 (7, 4) card_13, placed 4 (6, 3) card_137, placed 6 (6, 8) card_332, inline_634] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_660 : Valid card_660 := by
  rw [eq_card_660]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_137
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_332
  subst c
  exact valid_inline_634

theorem eq_inline_635 : inline_635 = combine (4, 3) [placed 6 (5, 7) card_9, placed 7 (7, 6) card_115, placed 7 (7, 7) card_302, placed 7 (7, 7) card_303] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_635 : Valid inline_635 := by
  rw [eq_inline_635]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 7) valid_302
  subst c
  exact placed_valid 7 (7, 7) valid_303

theorem eq_card_661 : card_661 = combine (4, 6) [placed 0 (3, 2) card_13, placed 4 (5, 2) card_14, placed 0 (3, 2) card_33, placed 1 (1, 3) card_116, inline_635] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_661 : Valid card_661 := by
  rw [eq_card_661]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_116
  subst c
  exact valid_inline_635

theorem eq_inline_636 : inline_636 = combine (1, 5) [placed 2 (1, 5) card_5, placed 4 (4, 2) card_141] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_636 : Valid inline_636 := by
  rw [eq_inline_636]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_5
  subst c
  exact placed_valid 4 (4, 2) valid_141

theorem eq_card_662 : card_662 = combine (4, 4) [placed 5 (1, 5) card_52, placed 0 (2, 0) card_658, inline_636] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_662 : Valid card_662 := by
  rw [eq_card_662]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_658
  subst c
  exact valid_inline_636

theorem eq_card_663 : card_663 = combine (4, 5) [placed 2 (1, 7) card_134, placed 2 (1, 7) card_180, placed 2 (1, 8) card_435, placed 0 (1, 2) card_507, placed 2 (2, 7) card_558, placed 2 (1, 9) card_562, placed 0 (1, 3) card_580, placed 0 (0, 0) card_662] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_663 : Valid card_663 := by
  rw [eq_card_663]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_507
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_558
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_562
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_580
  subst c
  exact placed_valid 0 (0, 0) valid_662


end OAI.Snaky21.Certificate

theorem solution : Valid card_660 ∧ Valid card_661 ∧ Valid card_662 ∧ Valid card_663 ∧ True :=
  ⟨valid_660, valid_661, valid_662, valid_663, True.intro⟩
