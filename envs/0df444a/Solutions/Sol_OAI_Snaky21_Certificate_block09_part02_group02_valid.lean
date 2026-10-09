-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part02_group02_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:41:31.715754+00:00
-- url     : https://prove2.me/submissions/b5c4e200-d768-4719-b01f-4f2b8f636e3f

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part02_group00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part02_group01_valid
import Definitions.Def_Snaky21Data09
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_valid
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
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_25 : Valid card_25 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_26 : Valid card_26 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_49 : Valid card_49 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_80 : Valid card_80 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_111 : Valid card_111 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_113 : Valid card_113 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_115 : Valid card_115 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_123 : Valid card_123 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_136 : Valid card_136 := block02_valid.2.2.2.2.2.2.2.2.1
theorem valid_171 : Valid card_171 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_253 : Valid card_253 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_256 : Valid card_256 := block04_valid.1
theorem valid_292 : Valid card_292 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_332 : Valid card_332 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_345 : Valid card_345 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_378 : Valid card_378 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_398 : Valid card_398 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_421 : Valid card_421 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_434 : Valid card_434 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_521 : Valid card_521 := block08_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_522 : Valid card_522 := block08_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_530 : Valid card_530 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_533 : Valid card_533 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_534 : Valid card_534 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_577 : Valid card_577 := block09_part00_valid.2.1
theorem valid_604 : Valid card_604 := block09_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_609 : Valid card_609 := block09_part02_group00_valid.2.1
theorem valid_610 : Valid card_610 := block09_part02_group00_valid.2.2.1
theorem valid_615 : Valid card_615 := block09_part02_group01_valid.2.2.2.1

theorem eq_inline_509 : inline_509 = combine (2, 6) [placed 0 (2, 2) card_6, placed 3 (3, 3) card_123] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_509 : Valid inline_509 := by
  rw [eq_inline_509]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_6
  subst c
  exact placed_valid 3 (3, 3) valid_123

theorem eq_inline_510 : inline_510 = combine (2, 5) [placed 0 (2, 1) card_11, inline_509, placed 0 (1, 1) card_521] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_510 : Valid inline_510 := by
  rw [eq_inline_510]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_11
  rcases hc with rfl | hc
  · exact valid_inline_509
  subst c
  exact placed_valid 0 (1, 1) valid_521

theorem eq_card_616 : card_616 = combine (3, 3) [placed 0 (0, 1) card_345, placed 1 (0, 2) card_421, placed 0 (0, 1) card_522, placed 0 (1, 0) card_530, placed 2 (0, 6) card_533, placed 0 (0, 0) card_534, inline_510] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_616 : Valid card_616 := by
  rw [eq_card_616]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_345
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_421
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_522
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_530
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_533
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_534
  subst c
  exact valid_inline_510

theorem eq_card_617 : card_617 = combine (4, 3) [placed 6 (5, 7) card_14, placed 2 (2, 6) card_136, placed 7 (7, 6) card_332, placed 0 (2, 1) card_616] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_617 : Valid card_617 := by
  rw [eq_card_617]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_136
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_332
  subst c
  exact placed_valid 0 (2, 1) valid_616

theorem eq_inline_511 : inline_511 = combine (3, 5) [placed 6 (3, 7) card_53, placed 1 (3, 3) card_378] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_511 : Valid inline_511 := by
  rw [eq_inline_511]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_53
  subst c
  exact placed_valid 1 (3, 3) valid_378

theorem eq_inline_512 : inline_512 = combine (3, 4) [placed 7 (6, 6) card_25, inline_511] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_512 : Valid inline_512 := by
  rw [eq_inline_512]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_25
  subst c
  exact valid_inline_511

theorem eq_inline_513 : inline_513 = combine (5, 6) [placed 0 (5, 2) card_7, placed 1 (4, 3) card_8, placed 4 (6, 2) card_9, inline_512] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_513 : Valid inline_513 := by
  rw [eq_inline_513]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_9
  subst c
  exact valid_inline_512

theorem eq_inline_514 : inline_514 = combine (5, 6) [placed 0 (5, 2) card_7, placed 1 (4, 3) card_8, placed 4 (6, 2) card_9, placed 1 (2, 3) card_604] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_514 : Valid inline_514 := by
  rw [eq_inline_514]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_9
  subst c
  exact placed_valid 1 (2, 3) valid_604

theorem eq_inline_515 : inline_515 = combine (5, 6) [placed 4 (6, 2) card_9, placed 1 (2, 3) card_171, placed 5 (3, 7) card_577, placed 6 (6, 7) card_609] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_515 : Valid inline_515 := by
  rw [eq_inline_515]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_171
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_577
  subst c
  exact placed_valid 6 (6, 7) valid_609

theorem eq_inline_516 : inline_516 = combine (5, 6) [placed 4 (6, 2) card_9, placed 3 (8, 3) card_256, placed 5 (3, 7) card_577] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_516 : Valid inline_516 := by
  rw [eq_inline_516]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_256
  subst c
  exact placed_valid 5 (3, 7) valid_577

theorem eq_inline_517 : inline_517 = combine (6, 4) [placed 6 (6, 4) card_4, placed 1 (1, 4) card_113] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_517 : Valid inline_517 := by
  rw [eq_inline_517]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 4) valid_4
  subst c
  exact placed_valid 1 (1, 4) valid_113

theorem eq_inline_518 : inline_518 = combine (3, 4) [placed 0 (2, 4) card_5, inline_517] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_518 : Valid inline_518 := by
  rw [eq_inline_518]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_5
  subst c
  exact valid_inline_517

theorem eq_inline_519 : inline_519 = combine (4, 4) [placed 3 (6, 3) card_80, placed 1 (2, 2) card_111, placed 0 (3, 1) card_616, inline_518] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_519 : Valid inline_519 := by
  rw [eq_inline_519]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_80
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_111
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_616
  subst c
  exact valid_inline_518

theorem eq_card_618 : card_618 = combine (5, 5) [placed 1 (2, 3) card_398, placed 0 (1, 2) card_434, placed 4 (6, 1) card_610, inline_513, inline_514, inline_515, inline_516, placed 0 (2, 0) card_615, inline_519] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_618 : Valid card_618 := by
  rw [eq_card_618]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_398
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_610
  rcases hc with rfl | hc
  · exact valid_inline_513
  rcases hc with rfl | hc
  · exact valid_inline_514
  rcases hc with rfl | hc
  · exact valid_inline_515
  rcases hc with rfl | hc
  · exact valid_inline_516
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_615
  subst c
  exact valid_inline_519

theorem eq_inline_520 : inline_520 = combine (2, 2) [placed 4 (4, 0) card_56, placed 0 (1, 0) card_253] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_520 : Valid inline_520 := by
  rw [eq_inline_520]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_56
  subst c
  exact placed_valid 0 (1, 0) valid_253

theorem eq_card_619 : card_619 = combine (4, 3) [placed 0 (1, 2) card_8, placed 0 (1, 2) card_26, placed 0 (1, 2) card_49, placed 0 (1, 0) card_115, placed 0 (1, 0) card_292, inline_520] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_619 : Valid card_619 := by
  rw [eq_card_619]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_49
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_292
  subst c
  exact valid_inline_520


end OAI.Snaky21.Certificate

theorem solution : Valid card_616 ∧ Valid card_617 ∧ Valid card_618 ∧ Valid card_619 ∧ True :=
  ⟨valid_616, valid_617, valid_618, valid_619, True.intro⟩
