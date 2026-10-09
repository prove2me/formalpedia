-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part00_group02_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:02:47.400997+00:00
-- url     : https://prove2.me/submissions/7c3501fe-6954-4ae9-b31e-ced5d00688dd

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_group01_valid
import Definitions.Def_Snaky21Data10
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
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
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_19 : Valid card_19 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_20 : Valid card_20 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_29 : Valid card_29 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_46 : Valid card_46 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_55 : Valid card_55 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_63 : Valid card_63 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_78 : Valid card_78 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_84 : Valid card_84 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_85 : Valid card_85 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_94 : Valid card_94 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_174 : Valid card_174 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_257 : Valid card_257 := block04_valid.2.1
theorem valid_314 : Valid card_314 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_475 : Valid card_475 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_480 : Valid card_480 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_483 : Valid card_483 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_507 : Valid card_507 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_523 : Valid card_523 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_545 : Valid card_545 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_566 : Valid card_566 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_587 : Valid card_587 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_605 : Valid card_605 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_635 : Valid card_635 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_644 : Valid card_644 := block10_part00_group01_valid.1
theorem valid_647 : Valid card_647 := block10_part00_group01_valid.2.2.2.1

theorem eq_card_648 : card_648 = combine (4, 4) [placed 0 (1, 1) card_174, placed 0 (2, 1) card_475, placed 0 (1, 0) card_480, placed 4 (7, 0) card_480, placed 2 (2, 8) card_483, placed 0 (1, 1) card_566, placed 0 (2, 1) card_587, placed 2 (2, 8) card_587, placed 1 (1, 2) card_605, placed 0 (2, 0) card_635, placed 0 (0, 0) card_644, placed 0 (0, 0) card_647] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_648 : Valid card_648 := by
  rw [eq_card_648]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_174
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_480
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 0) valid_480
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_483
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_566
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_635
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_644
  subst c
  exact placed_valid 0 (0, 0) valid_647

theorem eq_inline_600 : inline_600 = combine (1, 3) [placed 0 (0, 3) card_0, placed 4 (4, 2) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_600 : Valid inline_600 := by
  rw [eq_inline_600]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_0
  subst c
  exact placed_valid 4 (4, 2) valid_78

theorem eq_inline_601 : inline_601 = combine (2, 3) [placed 7 (3, 6) card_5, inline_600] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_601 : Valid inline_601 := by
  rw [eq_inline_601]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_5
  subst c
  exact valid_inline_600

theorem eq_inline_602 : inline_602 = combine (3, 4) [placed 3 (3, 3) card_5, inline_601] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_602 : Valid inline_602 := by
  rw [eq_inline_602]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 3) valid_5
  subst c
  exact valid_inline_601

theorem eq_inline_603 : inline_603 = combine (2, 6) [placed 3 (5, 5) card_15, inline_602] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_603 : Valid inline_603 := by
  rw [eq_inline_603]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 5) valid_15
  subst c
  exact valid_inline_602

theorem eq_inline_604 : inline_604 = combine (3, 3) [placed 7 (4, 6) card_5, inline_603] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_604 : Valid inline_604 := by
  rw [eq_inline_604]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 6) valid_5
  subst c
  exact valid_inline_603

theorem eq_inline_605 : inline_605 = combine (3, 6) [placed 3 (4, 3) card_5, inline_604] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_605 : Valid inline_605 := by
  rw [eq_inline_605]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact valid_inline_604

theorem eq_inline_606 : inline_606 = combine (4, 6) [placed 0 (3, 2) card_19, placed 0 (3, 2) card_84, placed 1 (3, 3) card_314, inline_605] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_606 : Valid inline_606 := by
  rw [eq_inline_606]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_84
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_314
  subst c
  exact valid_inline_605

theorem eq_inline_607 : inline_607 = combine (4, 3) [placed 2 (3, 6) card_10, placed 4 (4, 2) card_44, placed 2 (3, 6) card_63, inline_606] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_607 : Valid inline_607 := by
  rw [eq_inline_607]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_63
  subst c
  exact valid_inline_606

theorem eq_card_649 : card_649 = combine (4, 4) [placed 5 (1, 5) card_52, placed 0 (1, 1) card_523, inline_607] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_649 : Valid card_649 := by
  rw [eq_card_649]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_523
  subst c
  exact valid_inline_607

theorem eq_inline_608 : inline_608 = combine (5, 4) [placed 5 (2, 5) card_52, placed 4 (6, 0) card_545] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_608 : Valid inline_608 := by
  rw [eq_inline_608]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_52
  subst c
  exact placed_valid 4 (6, 0) valid_545

theorem eq_card_650 : card_650 = combine (5, 5) [placed 1 (1, 4) card_13, placed 1 (1, 4) card_14, placed 2 (2, 8) card_257, placed 2 (2, 8) card_435, placed 0 (2, 2) card_507, placed 2 (1, 10) card_649, inline_608] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_650 : Valid card_650 := by
  rw [eq_card_650]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_257
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_507
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_649
  subst c
  exact valid_inline_608

theorem eq_inline_609 : inline_609 = combine (3, 5) [placed 3 (6, 3) card_55, placed 7 (6, 6) card_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_609 : Valid inline_609 := by
  rw [eq_inline_609]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_55
  subst c
  exact placed_valid 7 (6, 6) valid_56

theorem eq_inline_610 : inline_610 = combine (3, 5) [placed 4 (4, 3) card_20, placed 0 (3, 3) card_29, placed 3 (5, 3) card_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_610 : Valid inline_610 := by
  rw [eq_inline_610]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_29
  subst c
  exact placed_valid 3 (5, 3) valid_46

theorem eq_inline_611 : inline_611 = combine (4, 3) [placed 7 (7, 5) card_85, placed 4 (4, 3) card_94] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_611 : Valid inline_611 := by
  rw [eq_inline_611]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_85
  subst c
  exact placed_valid 4 (4, 3) valid_94

theorem eq_card_651 : card_651 = combine (3, 6) [inline_609, inline_610, inline_611] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_651 : Valid card_651 := by
  rw [eq_card_651]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_609
  rcases hc with rfl | hc
  · exact valid_inline_610
  subst c
  exact valid_inline_611


end OAI.Snaky21.Certificate

theorem solution : Valid card_648 ∧ Valid card_649 ∧ Valid card_650 ∧ Valid card_651 ∧ True :=
  ⟨valid_648, valid_649, valid_650, valid_651, True.intro⟩
