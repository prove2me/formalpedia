-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part01_group00_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T13:17:15.224006+00:00
-- url     : https://prove2.me/submissions/2e8a2bd9-93d4-429e-b158-c8b88329b192

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
theorem valid_1 : Valid card_1 := block00_valid.2.1
theorem valid_2 : Valid card_2 := block00_valid.2.2.1
theorem valid_3 : Valid card_3 := block00_valid.2.2.2.1
theorem valid_4 : Valid card_4 := block00_valid.2.2.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_36 : Valid card_36 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_91 : Valid card_91 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_105 : Valid card_105 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_150 : Valid card_150 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_153 : Valid card_153 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_157 : Valid card_157 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_158 : Valid card_158 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_208 : Valid card_208 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_250 : Valid card_250 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_268 : Valid card_268 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_272 : Valid card_272 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_290 : Valid card_290 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_375 : Valid card_375 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem eq_inline_405 : inline_405 = combine (1, 5) [placed 1 (0, 1) card_1, placed 2 (1, 6) card_158] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_405 : Valid inline_405 := by
  rw [eq_inline_405]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_1
  subst c
  exact placed_valid 2 (1, 6) valid_158

theorem eq_card_592 : card_592 = combine (1, 4) [placed 2 (0, 5) card_22, placed 6 (1, 4) card_36, placed 0 (0, 0) card_150, inline_405] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_592 : Valid card_592 := by
  rw [eq_card_592]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 4) valid_36
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_150
  subst c
  exact valid_inline_405

theorem eq_inline_406 : inline_406 = combine (4, 5) [placed 0 (3, 2) card_36, placed 0 (3, 1) card_105, placed 2 (3, 6) card_250, placed 2 (3, 6) card_592] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_406 : Valid inline_406 := by
  rw [eq_inline_406]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_36
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_105
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_250
  subst c
  exact placed_valid 2 (3, 6) valid_592

theorem eq_card_593 : card_593 = combine (4, 3) [placed 0 (0, 2) card_2, inline_406] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_593 : Valid card_593 := by
  rw [eq_card_593]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_2
  subst c
  exact valid_inline_406

theorem eq_inline_407 : inline_407 = combine (5, 5) [placed 3 (5, 3) card_5, placed 0 (4, 3) card_91] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_407 : Valid inline_407 := by
  rw [eq_inline_407]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_5
  subst c
  exact placed_valid 0 (4, 3) valid_91

theorem eq_inline_408 : inline_408 = combine (5, 2) [placed 1 (5, 1) card_5, placed 2 (5, 5) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_408 : Valid inline_408 := by
  rw [eq_inline_408]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 1) valid_5
  subst c
  exact placed_valid 2 (5, 5) valid_6

theorem eq_inline_409 : inline_409 = combine (5, 5) [placed 3 (5, 3) card_5, inline_408] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_409 : Valid inline_409 := by
  rw [eq_inline_409]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_5
  subst c
  exact valid_inline_408

theorem eq_inline_410 : inline_410 = combine (5, 1) [placed 5 (1, 5) card_375, inline_409] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_410 : Valid inline_410 := by
  rw [eq_inline_410]
  apply combination_rule (5, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_375
  subst c
  exact valid_inline_409

theorem eq_inline_411 : inline_411 = combine (1, 2) [placed 7 (2, 6) card_4, inline_410] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_411 : Valid inline_411 := by
  rw [eq_inline_411]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 6) valid_4
  subst c
  exact valid_inline_410

theorem eq_inline_412 : inline_412 = combine (2, 5) [placed 6 (2, 7) card_7, placed 1 (1, 3) card_208, inline_411] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_412 : Valid inline_412 := by
  rw [eq_inline_412]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_208
  subst c
  exact valid_inline_411

theorem eq_inline_413 : inline_413 = combine (2, 3) [placed 0 (2, 3) card_1, inline_412] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_413 : Valid inline_413 := by
  rw [eq_inline_413]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_1
  subst c
  exact valid_inline_412

theorem eq_inline_414 : inline_414 = combine (2, 3) [placed 0 (2, 3) card_1, placed 0 (1, 1) card_268] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_414 : Valid inline_414 := by
  rw [eq_inline_414]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_1
  subst c
  exact placed_valid 0 (1, 1) valid_268

theorem eq_inline_415 : inline_415 = combine (2, 6) [placed 3 (6, 3) card_272, placed 7 (6, 7) card_290, inline_413, inline_414, placed 3 (7, 3) card_593] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_415 : Valid inline_415 := by
  rw [eq_inline_415]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_272
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_290
  rcases hc with rfl | hc
  · exact valid_inline_413
  rcases hc with rfl | hc
  · exact valid_inline_414
  subst c
  exact placed_valid 3 (7, 3) valid_593

theorem eq_card_594 : card_594 = combine (6, 4) [placed 7 (8, 4) card_53, inline_407, inline_415] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_594 : Valid card_594 := by
  rw [eq_card_594]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 4) valid_53
  rcases hc with rfl | hc
  · exact valid_inline_407
  subst c
  exact valid_inline_415

theorem eq_inline_416 : inline_416 = combine (4, 1) [placed 2 (1, 1) card_4, placed 2 (2, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_416 : Valid inline_416 := by
  rw [eq_inline_416]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 1) valid_4
  subst c
  exact placed_valid 2 (2, 1) valid_5

theorem eq_inline_417 : inline_417 = combine (5, 0) [placed 7 (6, 4) card_3, inline_416] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_417 : Valid inline_417 := by
  rw [eq_inline_417]
  apply combination_rule (5, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_3
  subst c
  exact valid_inline_416

theorem eq_inline_418 : inline_418 = combine (5, 1) [placed 7 (6, 5) card_4, inline_417] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_418 : Valid inline_418 := by
  rw [eq_inline_418]
  apply combination_rule (5, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_4
  subst c
  exact valid_inline_417

theorem eq_inline_419 : inline_419 = combine (2, 1) [placed 0 (0, 1) card_5, inline_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_419 : Valid inline_419 := by
  rw [eq_inline_419]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_418

theorem eq_inline_420 : inline_420 = combine (4, 2) [placed 0 (0, 1) card_2, placed 7 (7, 5) card_208] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_420 : Valid inline_420 := by
  rw [eq_inline_420]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact placed_valid 7 (7, 5) valid_208

theorem eq_inline_421 : inline_421 = combine (4, 2) [placed 6 (6, 2) card_5, placed 1 (3, 1) card_153] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_421 : Valid inline_421 := by
  rw [eq_inline_421]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 2) valid_5
  subst c
  exact placed_valid 1 (3, 1) valid_153

theorem eq_inline_422 : inline_422 = combine (5, 2) [placed 7 (6, 5) card_5, inline_421] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_422 : Valid inline_422 := by
  rw [eq_inline_422]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_5
  subst c
  exact valid_inline_421

theorem eq_inline_423 : inline_423 = combine (4, 2) [placed 0 (0, 1) card_2, placed 7 (7, 5) card_157] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_423 : Valid inline_423 := by
  rw [eq_inline_423]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact placed_valid 7 (7, 5) valid_157

theorem eq_inline_424 : inline_424 = combine (6, 2) [placed 7 (7, 5) card_8, inline_419, inline_420, inline_422, inline_423] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_424 : Valid inline_424 := by
  rw [eq_inline_424]
  apply combination_rule (6, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_8
  rcases hc with rfl | hc
  · exact valid_inline_419
  rcases hc with rfl | hc
  · exact valid_inline_420
  rcases hc with rfl | hc
  · exact valid_inline_422
  subst c
  exact valid_inline_423

theorem eq_inline_425 : inline_425 = combine (6, 3) [placed 2 (3, 4) card_5, inline_424] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_425 : Valid inline_425 := by
  rw [eq_inline_425]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_5
  subst c
  exact valid_inline_424

theorem eq_inline_426 : inline_426 = combine (6, 4) [placed 0 (3, 4) card_5, inline_425] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_426 : Valid inline_426 := by
  rw [eq_inline_426]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_5
  subst c
  exact valid_inline_425

theorem eq_card_595 : card_595 = combine (6, 5) [placed 0 (2, 4) card_4, inline_426] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_595 : Valid card_595 := by
  rw [eq_card_595]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_4
  subst c
  exact valid_inline_426


end OAI.Snaky21.Certificate

theorem solution : Valid card_592 ∧ Valid card_593 ∧ Valid card_594 ∧ Valid card_595 ∧ True :=
  ⟨valid_592, valid_593, valid_594, valid_595, True.intro⟩
