-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part00_group03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:14:27.122292+00:00
-- url     : https://prove2.me/submissions/12a9d67f-e69a-4cbe-9581-cc66e74aba9a

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_group02_valid
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
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_36 : Valid card_36 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_179 : Valid card_179 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_206 : Valid card_206 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_222 : Valid card_222 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_245 : Valid card_245 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_248 : Valid card_248 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_300 : Valid card_300 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_301 : Valid card_301 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_314 : Valid card_314 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_344 : Valid card_344 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_405 : Valid card_405 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_436 : Valid card_436 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_449 : Valid card_449 := block07_valid.2.1
theorem valid_502 : Valid card_502 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_509 : Valid card_509 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_510 : Valid card_510 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_558 : Valid card_558 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_651 : Valid card_651 := block10_part00_group02_valid.2.2.2.1

theorem eq_inline_612 : inline_612 = combine (3, 5) [placed 6 (5, 5) card_0, placed 4 (5, 2) card_245] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_612 : Valid inline_612 := by
  rw [eq_inline_612]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 5) valid_0
  subst c
  exact placed_valid 4 (5, 2) valid_245

theorem eq_inline_613 : inline_613 = combine (4, 5) [placed 1 (1, 4) card_36, placed 6 (4, 6) card_44, inline_612] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_613 : Valid inline_613 := by
  rw [eq_inline_613]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_36
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_44
  subst c
  exact valid_inline_612

theorem eq_inline_614 : inline_614 = combine (4, 4) [placed 5 (0, 5) card_222, inline_613] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_614 : Valid inline_614 := by
  rw [eq_inline_614]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_222
  subst c
  exact valid_inline_613

theorem eq_inline_615 : inline_615 = combine (2, 5) [placed 4 (3, 2) card_10, placed 1 (0, 3) card_558, inline_614] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_615 : Valid inline_615 := by
  rw [eq_inline_615]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_558
  subst c
  exact valid_inline_614

theorem eq_card_652 : card_652 = combine (4, 3) [placed 4 (5, 3) card_0, inline_615] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_652 : Valid card_652 := by
  rw [eq_card_652]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_0
  subst c
  exact valid_inline_615

theorem eq_inline_616 : inline_616 = combine (4, 4) [placed 1 (0, 3) card_206, placed 0 (2, 1) card_301, placed 3 (5, 3) card_405] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_616 : Valid inline_616 := by
  rw [eq_inline_616]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_206
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_301
  subst c
  exact placed_valid 3 (5, 3) valid_405

theorem eq_card_653 : card_653 = combine (2, 4) [placed 5 (0, 4) card_53, placed 3 (6, 3) card_53, placed 0 (1, 0) card_652, inline_616] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_653 : Valid card_653 := by
  rw [eq_card_653]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_652
  subst c
  exact valid_inline_616

theorem eq_inline_617 : inline_617 = combine (4, 6) [placed 7 (4, 7) card_0, placed 5 (1, 7) card_502] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_617 : Valid inline_617 := by
  rw [eq_inline_617]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_0
  subst c
  exact placed_valid 5 (1, 7) valid_502

theorem eq_inline_618 : inline_618 = combine (4, 5) [placed 0 (3, 1) card_53, placed 6 (4, 7) card_53, placed 6 (7, 8) card_651, inline_617] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_618 : Valid inline_618 := by
  rw [eq_inline_618]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_651
  subst c
  exact valid_inline_617

theorem eq_card_654 : card_654 = combine (4, 4) [placed 1 (0, 2) card_248, placed 1 (0, 2) card_300, placed 1 (0, 1) card_436, placed 2 (1, 7) card_449, placed 0 (1, 1) card_509, placed 2 (1, 7) card_510, placed 5 (0, 7) card_653, inline_618] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_654 : Valid card_654 := by
  rw [eq_card_654]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_248
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_300
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_436
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_449
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_509
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_510
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_653
  subst c
  exact valid_inline_618

theorem eq_inline_619 : inline_619 = combine (3, 6) [placed 3 (5, 2) card_179, placed 1 (2, 3) card_314, placed 7 (5, 7) card_344] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_619 : Valid inline_619 := by
  rw [eq_inline_619]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 2) valid_179
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_314
  subst c
  exact placed_valid 7 (5, 7) valid_344

theorem eq_card_655 : card_655 = combine (3, 3) [placed 2 (2, 6) card_10, placed 4 (3, 2) card_52, placed 7 (6, 6) card_435, inline_619] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_655 : Valid card_655 := by
  rw [eq_card_655]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_435
  subst c
  exact valid_inline_619


end OAI.Snaky21.Certificate

theorem solution : Valid card_652 ∧ Valid card_653 ∧ Valid card_654 ∧ Valid card_655 ∧ True :=
  ⟨valid_652, valid_653, valid_654, valid_655, True.intro⟩
