-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part00_group00_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:00:28.826103+00:00
-- url     : https://prove2.me/submissions/095a1d9c-90fc-476f-9b20-5198ea733fc1

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
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
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_47 : Valid card_47 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_60 : Valid card_60 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_61 : Valid card_61 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_89 : Valid card_89 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_90 : Valid card_90 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_144 : Valid card_144 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_183 : Valid card_183 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_260 : Valid card_260 := block04_valid.2.2.2.2.1
theorem valid_299 : Valid card_299 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_349 : Valid card_349 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_476 : Valid card_476 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_587 : Valid card_587 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_612 : Valid card_612 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem eq_inline_588 : inline_588 = combine (5, 6) [placed 1 (4, 3) card_5, placed 0 (2, 5) card_90] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_588 : Valid inline_588 := by
  rw [eq_inline_588]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 3) valid_5
  subst c
  exact placed_valid 0 (2, 5) valid_90

theorem eq_inline_589 : inline_589 = combine (2, 6) [placed 5 (1, 6) card_44, placed 3 (5, 3) card_260, inline_588] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_589 : Valid inline_589 := by
  rw [eq_inline_589]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_260
  subst c
  exact valid_inline_588

theorem eq_inline_590 : inline_590 = combine (4, 6) [placed 3 (4, 3) card_5, inline_589] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_590 : Valid inline_590 := by
  rw [eq_inline_590]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact valid_inline_589

theorem eq_inline_591 : inline_591 = combine (3, 6) [placed 4 (4, 2) card_61, placed 2 (3, 6) card_89, placed 3 (6, 2) card_183, inline_590] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_591 : Valid inline_591 := by
  rw [eq_inline_591]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_61
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_89
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_183
  subst c
  exact valid_inline_590

theorem eq_card_640 : card_640 = combine (4, 5) [placed 0 (3, 2) card_10, placed 5 (2, 6) card_47, placed 6 (4, 6) card_52, inline_591] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_640 : Valid card_640 := by
  rw [eq_card_640]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 6) valid_47
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_52
  subst c
  exact valid_inline_591

theorem eq_inline_592 : inline_592 = combine (3, 4) [placed 0 (2, 0) card_14, placed 1 (0, 3) card_44, placed 4 (4, 1) card_60] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_592 : Valid inline_592 := by
  rw [eq_inline_592]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_44
  subst c
  exact placed_valid 4 (4, 1) valid_60

theorem eq_card_641 : card_641 = combine (2, 3) [placed 5 (0, 3) card_52, placed 0 (1, 1) card_144, inline_592] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_641 : Valid card_641 := by
  rw [eq_card_641]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_144
  subst c
  exact valid_inline_592

theorem eq_card_642 : card_642 = combine (3, 5) [placed 0 (0, 1) card_299, placed 0 (0, 1) card_349, placed 0 (0, 1) card_476, placed 0 (1, 1) card_587, placed 2 (1, 8) card_587, placed 5 (0, 5) card_612, placed 0 (0, 2) card_641] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_642 : Valid card_642 := by
  rw [eq_card_642]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_299
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_349
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_476
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_612
  subst c
  exact placed_valid 0 (0, 2) valid_641

theorem eq_card_643 : card_643 = combine (3, 5) [placed 2 (0, 8) card_299, placed 2 (0, 8) card_349, placed 2 (0, 8) card_476, placed 0 (1, 1) card_587, placed 2 (1, 8) card_587, placed 1 (0, 4) card_612, placed 2 (0, 7) card_641] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_643 : Valid card_643 := by
  rw [eq_card_643]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_299
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_349
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_476
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_612
  subst c
  exact placed_valid 2 (0, 7) valid_641


end OAI.Snaky21.Certificate

theorem solution : Valid card_640 ∧ Valid card_641 ∧ Valid card_642 ∧ Valid card_643 ∧ True :=
  ⟨valid_640, valid_641, valid_642, valid_643, True.intro⟩
