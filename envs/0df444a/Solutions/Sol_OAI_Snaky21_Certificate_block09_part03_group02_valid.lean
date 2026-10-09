-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part03_group02_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:50:09.763618+00:00
-- url     : https://prove2.me/submissions/c107a522-34b7-47df-89cb-4babc5e62839

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part03_group01_valid
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
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_27 : Valid card_27 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_33 : Valid card_33 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_47 : Valid card_47 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_50 : Valid card_50 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_54 : Valid card_54 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_82 : Valid card_82 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_92 : Valid card_92 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_93 : Valid card_93 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_125 : Valid card_125 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_144 : Valid card_144 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_181 : Valid card_181 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_294 : Valid card_294 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_378 : Valid card_378 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_395 : Valid card_395 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_438 : Valid card_438 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_452 : Valid card_452 := block07_valid.2.2.2.2.1
theorem valid_454 : Valid card_454 := block07_valid.2.2.2.2.2.2.1
theorem valid_455 : Valid card_455 := block07_valid.2.2.2.2.2.2.2.1
theorem valid_587 : Valid card_587 := block09_part00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_589 : Valid card_589 := block09_part00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_612 : Valid card_612 := block09_part02_valid.2.2.2.2.1

theorem valid_631 : Valid card_631 := block09_part03_group01_valid.2.2.2.1

theorem eq_inline_566 : inline_566 = combine (3, 2) [placed 5 (1, 5) card_92, placed 1 (1, 2) card_378] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_566 : Valid inline_566 := by
  rw [eq_inline_566]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_92
  subst c
  exact placed_valid 1 (1, 2) valid_378

theorem eq_inline_567 : inline_567 = combine (3, 5) [placed 4 (4, 2) card_10, placed 2 (3, 6) card_52, placed 0 (0, 2) card_82, inline_566] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_567 : Valid inline_567 := by
  rw [eq_inline_567]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_82
  subst c
  exact valid_inline_566

theorem eq_inline_568 : inline_568 = combine (3, 4) [placed 5 (0, 4) card_54, placed 3 (6, 2) card_294, inline_567, placed 0 (0, 0) card_631] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_568 : Valid inline_568 := by
  rw [eq_inline_568]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_294
  rcases hc with rfl | hc
  · exact valid_inline_567
  subst c
  exact placed_valid 0 (0, 0) valid_631

theorem eq_card_632 : card_632 = combine (3, 3) [placed 5 (0, 4) card_50, placed 5 (0, 4) card_125, placed 3 (5, 2) card_454, placed 0 (1, 2) card_455, inline_568] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_632 : Valid card_632 := by
  rw [eq_card_632]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 2) valid_454
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_455
  subst c
  exact valid_inline_568

theorem eq_inline_569 : inline_569 = combine (5, 3) [placed 1 (4, 3) card_8, placed 5 (4, 6) card_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_569 : Valid inline_569 := by
  rw [eq_inline_569]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 3) valid_8
  subst c
  exact placed_valid 5 (4, 6) valid_93

theorem eq_inline_570 : inline_570 = combine (5, 6) [placed 4 (5, 3) card_27, placed 6 (5, 7) card_52, placed 5 (3, 6) card_144, inline_569] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_570 : Valid inline_570 := by
  rw [eq_inline_570]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_144
  subst c
  exact valid_inline_569

theorem eq_card_633 : card_633 = combine (4, 4) [placed 6 (6, 6) card_47, placed 6 (5, 6) card_144, inline_570] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_633 : Valid card_633 := by
  rw [eq_card_633]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 6) valid_47
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_144
  subst c
  exact valid_inline_570

theorem eq_card_634 : card_634 = combine (5, 5) [placed 0 (0, 1) card_438, placed 0 (0, 1) card_452, placed 2 (3, 8) card_587, placed 7 (6, 5) card_612, placed 0 (0, 0) card_633] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_634 : Valid card_634 := by
  rw [eq_card_634]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_438
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_612
  subst c
  exact placed_valid 0 (0, 0) valid_633

theorem eq_inline_571 : inline_571 = combine (2, 6) [placed 4 (2, 2) card_7, placed 0 (1, 2) card_9, placed 1 (0, 3) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_571 : Valid inline_571 := by
  rw [eq_inline_571]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_9
  subst c
  exact placed_valid 1 (0, 3) valid_395

theorem eq_card_635 : card_635 = combine (2, 3) [placed 2 (1, 7) card_14, placed 6 (3, 7) card_33, placed 5 (0, 6) card_181, placed 5 (0, 6) card_589, inline_571] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_635 : Valid card_635 := by
  rw [eq_card_635]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_589
  subst c
  exact valid_inline_571


end OAI.Snaky21.Certificate

theorem solution : Valid card_632 ∧ Valid card_633 ∧ Valid card_634 ∧ Valid card_635 ∧ True :=
  ⟨valid_632, valid_633, valid_634, valid_635, True.intro⟩
