-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part02_group00_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:39:08.014004+00:00
-- url     : https://prove2.me/submissions/8c48076c-16fe-471f-a2f4-14e5040985f3

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
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
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_17 : Valid card_17 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_18 : Valid card_18 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_19 : Valid card_19 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_25 : Valid card_25 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_27 : Valid card_27 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_28 : Valid card_28 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_31 : Valid card_31 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_42 : Valid card_42 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_47 : Valid card_47 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_48 : Valid card_48 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_54 : Valid card_54 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_58 : Valid card_58 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_93 : Valid card_93 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_197 : Valid card_197 := block03_valid.2.2.2.2.2.1
theorem valid_225 : Valid card_225 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_355 : Valid card_355 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_364 : Valid card_364 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_375 : Valid card_375 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_434 : Valid card_434 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem eq_inline_486 : inline_486 = combine (5, 3) [placed 4 (5, 3) card_18, placed 7 (5, 6) card_375] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_486 : Valid inline_486 := by
  rw [eq_inline_486]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_18
  subst c
  exact placed_valid 7 (5, 6) valid_375

theorem eq_inline_487 : inline_487 = combine (2, 5) [placed 7 (5, 6) card_28, placed 6 (2, 6) card_42] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_487 : Valid inline_487 := by
  rw [eq_inline_487]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_28
  subst c
  exact placed_valid 6 (2, 6) valid_42

theorem eq_inline_488 : inline_488 = combine (2, 5) [placed 6 (2, 6) card_42, placed 0 (1, 3) card_58] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_488 : Valid inline_488 := by
  rw [eq_inline_488]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_42
  subst c
  exact placed_valid 0 (1, 3) valid_58

theorem eq_inline_489 : inline_489 = combine (1, 2) [inline_486, inline_487, inline_488] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_489 : Valid inline_489 := by
  rw [eq_inline_489]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_486
  rcases hc with rfl | hc
  · exact valid_inline_487
  subst c
  exact valid_inline_488

theorem eq_card_608 : card_608 = combine (4, 6) [placed 2 (3, 8) card_13, placed 2 (3, 8) card_31, placed 2 (1, 7) card_355, placed 0 (1, 2) card_364, placed 0 (0, 3) card_434, inline_489] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_608 : Valid card_608 := by
  rw [eq_card_608]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_355
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_364
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_434
  subst c
  exact valid_inline_489

theorem eq_inline_490 : inline_490 = combine (2, 1) [placed 5 (1, 4) card_5, placed 5 (0, 2) card_48] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_490 : Valid inline_490 := by
  rw [eq_inline_490]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 5 (0, 2) valid_48

theorem eq_inline_491 : inline_491 = combine (3, 3) [placed 1 (0, 1) card_25, placed 0 (3, 0) card_54] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_491 : Valid inline_491 := by
  rw [eq_inline_491]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_25
  subst c
  exact placed_valid 0 (3, 0) valid_54

theorem eq_card_609 : card_609 = combine (3, 1) [inline_490, inline_491] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_609 : Valid card_609 := by
  rw [eq_card_609]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_490
  subst c
  exact valid_inline_491

theorem eq_card_610 : card_610 = combine (1, 5) [placed 0 (0, 1) card_19, placed 3 (2, 2) card_197, placed 0 (0, 1) card_225, placed 2 (0, 6) card_609] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_610 : Valid card_610 := by
  rw [eq_card_610]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 2) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_225
  subst c
  exact placed_valid 2 (0, 6) valid_609

theorem eq_inline_492 : inline_492 = combine (2, 3) [placed 2 (2, 7) card_7, placed 0 (1, 3) card_17, placed 5 (1, 6) card_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_492 : Valid inline_492 := by
  rw [eq_inline_492]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_17
  subst c
  exact placed_valid 5 (1, 6) valid_93

theorem eq_card_611 : card_611 = combine (2, 5) [placed 4 (2, 3) card_27, placed 5 (0, 7) card_47, inline_492] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_611 : Valid card_611 := by
  rw [eq_card_611]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 3) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_47
  subst c
  exact valid_inline_492


end OAI.Snaky21.Certificate

theorem solution : Valid card_608 ∧ Valid card_609 ∧ Valid card_610 ∧ Valid card_611 ∧ True :=
  ⟨valid_608, valid_609, valid_610, valid_611, True.intro⟩
