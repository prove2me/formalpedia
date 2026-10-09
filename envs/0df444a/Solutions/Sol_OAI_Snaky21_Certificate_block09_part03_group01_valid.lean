-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part03_group01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:48:29.508408+00:00
-- url     : https://prove2.me/submissions/ee7cd1f0-3f93-40b6-bbd2-cba7d501d5f5

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part03_group00_valid
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
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_34 : Valid card_34 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_36 : Valid card_36 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_43 : Valid card_43 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_45 : Valid card_45 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_51 : Valid card_51 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_63 : Valid card_63 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_112 : Valid card_112 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_126 : Valid card_126 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_181 : Valid card_181 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_190 : Valid card_190 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_257 : Valid card_257 := block04_valid.2.1
theorem valid_265 : Valid card_265 := block04_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_270 : Valid card_270 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_295 : Valid card_295 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_355 : Valid card_355 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_356 : Valid card_356 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_363 : Valid card_363 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_364 : Valid card_364 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_368 : Valid card_368 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_398 : Valid card_398 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_418 : Valid card_418 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_434 : Valid card_434 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_441 : Valid card_441 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_464 : Valid card_464 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_466 : Valid card_466 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_467 : Valid card_467 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_518 : Valid card_518 := block08_valid.2.2.2.2.2.2.1

theorem valid_627 : Valid card_627 := block09_part03_group00_valid.2.2.2.1

theorem eq_inline_556 : inline_556 = combine (3, 2) [placed 7 (4, 3) card_36, placed 0 (3, 0) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_556 : Valid inline_556 := by
  rw [eq_inline_556]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 3) valid_36
  subst c
  exact placed_valid 0 (3, 0) valid_53

theorem eq_inline_557 : inline_557 = combine (3, 4) [placed 7 (5, 4) card_34, placed 4 (4, 0) card_464] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_557 : Valid inline_557 := by
  rw [eq_inline_557]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_34
  subst c
  exact placed_valid 4 (4, 0) valid_464

theorem eq_inline_558 : inline_558 = combine (2, 3) [placed 6 (4, 3) card_5, placed 5 (1, 4) card_265] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_558 : Valid inline_558 := by
  rw [eq_inline_558]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_5
  subst c
  exact placed_valid 5 (1, 4) valid_265

theorem eq_card_628 : card_628 = combine (3, 3) [placed 1 (0, 2) card_126, placed 2 (1, 5) card_270, inline_556, inline_557, inline_558] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_628 : Valid card_628 := by
  rw [eq_card_628]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_126
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_270
  rcases hc with rfl | hc
  · exact valid_inline_556
  rcases hc with rfl | hc
  · exact valid_inline_557
  subst c
  exact valid_inline_558

theorem eq_card_629 : card_629 = combine (3, 5) [placed 4 (5, 1) card_190, placed 4 (7, 2) card_295, placed 4 (6, 1) card_364, placed 0 (0, 0) card_518, placed 2 (2, 7) card_628] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_629 : Valid card_629 := by
  rw [eq_card_629]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_295
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_364
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_518
  subst c
  exact placed_valid 2 (2, 7) valid_628

theorem eq_inline_559 : inline_559 = combine (4, 8) [placed 0 (3, 4) card_12, placed 6 (5, 10) card_13, placed 6 (7, 9) card_355, placed 6 (7, 10) card_356, placed 4 (8, 5) card_434, placed 3 (7, 5) card_435, placed 2 (3, 10) card_441] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_559 : Valid inline_559 := by
  rw [eq_inline_559]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 10) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_355
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 10) valid_356
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 5) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_435
  subst c
  exact placed_valid 2 (3, 10) valid_441

theorem eq_inline_560 : inline_560 = combine (4, 5) [placed 0 (3, 3) card_13, placed 0 (3, 4) card_112, placed 6 (7, 9) card_363, placed 6 (7, 9) card_364] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_560 : Valid inline_560 := by
  rw [eq_inline_560]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_112
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_363
  subst c
  exact placed_valid 6 (7, 9) valid_364

theorem eq_inline_561 : inline_561 = combine (4, 5) [placed 0 (3, 4) card_112, placed 3 (6, 4) card_181, placed 5 (2, 8) card_181, placed 6 (8, 8) card_295, placed 0 (3, 4) card_466] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_561 : Valid inline_561 := by
  rw [eq_inline_561]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_112
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 8) valid_295
  subst c
  exact placed_valid 0 (3, 4) valid_466

theorem eq_inline_562 : inline_562 = combine (5, 7) [placed 6 (5, 8) card_10, placed 5 (3, 7) card_34] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_562 : Valid inline_562 := by
  rw [eq_inline_562]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_10
  subst c
  exact placed_valid 5 (3, 7) valid_34

theorem eq_inline_563 : inline_563 = combine (4, 5) [placed 0 (3, 4) card_112, placed 5 (1, 8) card_257, placed 7 (7, 7) card_398, inline_562, placed 0 (3, 3) card_628] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_563 : Valid inline_563 := by
  rw [eq_inline_563]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_112
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 8) valid_257
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 7) valid_398
  rcases hc with rfl | hc
  · exact valid_inline_562
  subst c
  exact placed_valid 0 (3, 3) valid_628

theorem eq_card_630 : card_630 = combine (4, 6) [placed 4 (8, 3) card_368, placed 6 (8, 10) card_368, inline_559, placed 6 (8, 11) card_467, placed 0 (1, 3) card_627, inline_560, inline_561, placed 2 (1, 10) card_629, inline_563] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_630 : Valid card_630 := by
  rw [eq_card_630]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_368
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 10) valid_368
  rcases hc with rfl | hc
  · exact valid_inline_559
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 11) valid_467
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_627
  rcases hc with rfl | hc
  · exact valid_inline_560
  rcases hc with rfl | hc
  · exact valid_inline_561
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_629
  subst c
  exact valid_inline_563

theorem eq_inline_564 : inline_564 = combine (3, 2) [placed 7 (5, 5) card_45, placed 1 (2, 2) card_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_564 : Valid inline_564 := by
  rw [eq_inline_564]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 5) valid_45
  subst c
  exact placed_valid 1 (2, 2) valid_418

theorem eq_inline_565 : inline_565 = combine (4, 2) [placed 2 (3, 5) card_43, placed 2 (3, 5) card_51, inline_564] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_565 : Valid inline_565 := by
  rw [eq_inline_565]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_43
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_51
  subst c
  exact valid_inline_564

theorem eq_card_631 : card_631 = combine (3, 5) [placed 2 (3, 6) card_44, placed 2 (3, 6) card_52, placed 4 (4, 2) card_63, inline_565] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_631 : Valid card_631 := by
  rw [eq_card_631]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_63
  subst c
  exact valid_inline_565


end OAI.Snaky21.Certificate

theorem solution : Valid card_628 ∧ Valid card_629 ∧ Valid card_630 ∧ Valid card_631 ∧ True :=
  ⟨valid_628, valid_629, valid_630, valid_631, True.intro⟩
