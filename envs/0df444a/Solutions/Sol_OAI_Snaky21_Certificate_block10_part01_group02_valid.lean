-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part01_group02_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:20:18.144796+00:00
-- url     : https://prove2.me/submissions/20096c67-8a2f-46bd-b3dd-9ed4a0b82c34

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_group01_valid
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
theorem valid_4 : Valid card_4 := block00_valid.2.2.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_40 : Valid card_40 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_70 : Valid card_70 := block01_valid.2.2.2.2.2.2.1
theorem valid_93 : Valid card_93 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_106 : Valid card_106 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_134 : Valid card_134 := block02_valid.2.2.2.2.2.2.1
theorem valid_180 : Valid card_180 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_257 : Valid card_257 := block04_valid.2.1
theorem valid_269 : Valid card_269 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_309 : Valid card_309 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_314 : Valid card_314 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_322 : Valid card_322 := block05_valid.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_459 : Valid card_459 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_517 : Valid card_517 := block08_valid.2.2.2.2.2.1
theorem valid_558 : Valid card_558 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_580 : Valid card_580 := block09_valid.2.2.2.2.1
theorem valid_588 : Valid card_588 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_662 : Valid card_662 := block10_part01_group01_valid.2.2.1

theorem eq_card_664 : card_664 = combine (6, 5) [placed 2 (3, 7) card_134, placed 2 (3, 7) card_180, placed 4 (7, 2) card_309, placed 2 (3, 8) card_435, placed 2 (4, 7) card_558, placed 0 (3, 3) card_580, placed 0 (2, 0) card_662] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_664 : Valid card_664 := by
  rw [eq_card_664]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_309
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_558
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_580
  subst c
  exact placed_valid 0 (2, 0) valid_662

theorem eq_inline_637 : inline_637 = combine (4, 7) [placed 6 (4, 7) card_70, placed 0 (3, 3) card_106, placed 0 (3, 3) card_269, placed 1 (0, 4) card_322] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_637 : Valid inline_637 := by
  rw [eq_inline_637]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_70
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_106
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_269
  subst c
  exact placed_valid 1 (0, 4) valid_322

theorem eq_inline_638 : inline_638 = combine (4, 7) [placed 6 (4, 7) card_70, placed 3 (7, 4) card_257, placed 3 (7, 4) card_435] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_638 : Valid inline_638 := by
  rw [eq_inline_638]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_70
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_257
  subst c
  exact placed_valid 3 (7, 4) valid_435

theorem eq_inline_639 : inline_639 = combine (3, 7) [placed 7 (3, 7) card_4, placed 3 (4, 4) card_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_639 : Valid inline_639 := by
  rw [eq_inline_639]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 7) valid_4
  subst c
  exact placed_valid 3 (4, 4) valid_93

theorem eq_inline_640 : inline_640 = combine (3, 4) [placed 7 (3, 6) card_5, inline_639] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_640 : Valid inline_640 := by
  rw [eq_inline_640]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_5
  subst c
  exact valid_inline_639

theorem eq_inline_641 : inline_641 = combine (3, 5) [placed 6 (4, 7) card_40, placed 1 (0, 4) card_517, inline_640] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_641 : Valid inline_641 := by
  rw [eq_inline_641]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_517
  subst c
  exact valid_inline_640

theorem eq_card_665 : card_665 = combine (4, 5) [placed 0 (3, 1) card_459, placed 5 (1, 7) card_588, inline_637, inline_638, inline_641] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_665 : Valid card_665 := by
  rw [eq_card_665]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_588
  rcases hc with rfl | hc
  · exact valid_inline_637
  rcases hc with rfl | hc
  · exact valid_inline_638
  subst c
  exact valid_inline_641

theorem eq_inline_642 : inline_642 = combine (1, 3) [placed 6 (4, 3) card_4, placed 0 (1, 2) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_642 : Valid inline_642 := by
  rw [eq_inline_642]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_4
  subst c
  exact placed_valid 0 (1, 2) valid_314

theorem eq_inline_643 : inline_643 = combine (4, 3) [placed 1 (3, 0) card_5, inline_642] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_643 : Valid inline_643 := by
  rw [eq_inline_643]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 0) valid_5
  subst c
  exact valid_inline_642

theorem eq_card_666 : card_666 = combine (2, 3) [placed 3 (3, 0) card_5, inline_643] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_666 : Valid card_666 := by
  rw [eq_card_666]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 0) valid_5
  subst c
  exact valid_inline_643

theorem eq_card_667 : card_667 = combine (3, 4) [placed 0 (3, 0) card_7, placed 4 (4, 0) card_9, placed 0 (0, 1) card_666] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_667 : Valid card_667 := by
  rw [eq_card_667]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_9
  subst c
  exact placed_valid 0 (0, 1) valid_666


end OAI.Snaky21.Certificate

theorem solution : Valid card_664 ∧ Valid card_665 ∧ Valid card_666 ∧ Valid card_667 ∧ True :=
  ⟨valid_664, valid_665, valid_666, valid_667, True.intro⟩
