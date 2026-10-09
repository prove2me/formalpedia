-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part03_group00_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:39:56.532358+00:00
-- url     : https://prove2.me/submissions/a31b1665-0b9c-45a3-8f57-0d5f9d5cb15d

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Definitions.Def_Snaky21Data10
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part02_valid
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
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_21 : Valid card_21 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_27 : Valid card_27 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_30 : Valid card_30 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_35 : Valid card_35 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_39 : Valid card_39 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_41 : Valid card_41 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_59 : Valid card_59 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_67 : Valid card_67 := block01_valid.2.2.2.1
theorem valid_80 : Valid card_80 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_102 : Valid card_102 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_175 : Valid card_175 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_228 : Valid card_228 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_253 : Valid card_253 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_256 : Valid card_256 := block04_valid.1
theorem valid_277 : Valid card_277 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_278 : Valid card_278 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_317 : Valid card_317 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_324 : Valid card_324 := block05_valid.2.2.2.2.1
theorem valid_336 : Valid card_336 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_373 : Valid card_373 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_400 : Valid card_400 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_460 : Valid card_460 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_462 : Valid card_462 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_463 : Valid card_463 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_488 : Valid card_488 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_686 : Valid card_686 := block10_part02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem eq_inline_719 : inline_719 = combine (3, 4) [placed 2 (0, 5) card_8, placed 5 (0, 5) card_41, placed 2 (0, 7) card_253, placed 2 (0, 7) card_256, placed 5 (0, 5) card_336] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_719 : Valid inline_719 := by
  rw [eq_inline_719]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_41
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_253
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_256
  subst c
  exact placed_valid 5 (0, 5) valid_336

theorem eq_card_688 : card_688 = combine (1, 5) [placed 1 (0, 1) card_0, inline_719] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_688 : Valid card_688 := by
  rw [eq_card_688]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_0
  subst c
  exact valid_inline_719

theorem eq_inline_720 : inline_720 = combine (4, 6) [placed 4 (5, 2) card_67, placed 6 (5, 8) card_175, placed 1 (1, 3) card_228, placed 3 (5, 3) card_373, placed 3 (7, 3) card_435, placed 1 (0, 4) card_688] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_720 : Valid inline_720 := by
  rw [eq_inline_720]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_175
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_228
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_373
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_435
  subst c
  exact placed_valid 1 (0, 4) valid_688

theorem eq_card_689 : card_689 = combine (4, 5) [placed 1 (1, 4) card_44, placed 4 (5, 0) card_324, placed 0 (0, 1) card_686, inline_720] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_689 : Valid card_689 := by
  rw [eq_card_689]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 0) valid_324
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_686
  subst c
  exact valid_inline_720

theorem eq_inline_721 : inline_721 = combine (3, 6) [placed 0 (2, 2) card_39, placed 0 (2, 2) card_80, placed 1 (0, 2) card_463] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_721 : Valid inline_721 := by
  rw [eq_inline_721]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_80
  subst c
  exact placed_valid 1 (0, 2) valid_463

theorem eq_card_690 : card_690 = combine (3, 4) [placed 1 (2, 3) card_21, placed 6 (5, 6) card_56, inline_721] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_690 : Valid card_690 := by
  rw [eq_card_690]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_56
  subst c
  exact valid_inline_721

theorem eq_inline_722 : inline_722 = combine (4, 5) [placed 2 (3, 6) card_27, placed 5 (1, 7) card_277, placed 1 (1, 3) card_278] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_722 : Valid inline_722 := by
  rw [eq_inline_722]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_277
  subst c
  exact placed_valid 1 (1, 3) valid_278

theorem eq_inline_723 : inline_723 = combine (5, 6) [placed 6 (7, 6) card_0, placed 0 (3, 2) card_317] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_723 : Valid inline_723 := by
  rw [eq_inline_723]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_0
  subst c
  exact placed_valid 0 (3, 2) valid_317

theorem eq_inline_724 : inline_724 = combine (6, 6) [placed 5 (3, 6) card_30, placed 2 (3, 9) card_59, placed 0 (5, 2) card_462, inline_723] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_724 : Valid inline_724 := by
  rw [eq_inline_724]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_462
  subst c
  exact valid_inline_723

theorem eq_inline_725 : inline_725 = combine (6, 5) [placed 5 (2, 6) card_102, placed 0 (2, 3) card_400, inline_724] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_725 : Valid inline_725 := by
  rw [eq_inline_725]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 6) valid_102
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_400
  subst c
  exact valid_inline_724

theorem eq_inline_726 : inline_726 = combine (4, 5) [placed 1 (3, 2) card_0, inline_725] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_726 : Valid inline_726 := by
  rw [eq_inline_726]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 2) valid_0
  subst c
  exact valid_inline_725

theorem eq_inline_727 : inline_727 = combine (4, 6) [placed 1 (3, 3) card_5, inline_726] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_727 : Valid inline_727 := by
  rw [eq_inline_727]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_5
  subst c
  exact valid_inline_726

theorem eq_inline_728 : inline_728 = combine (2, 6) [placed 3 (3, 3) card_5, placed 1 (2, 4) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_728 : Valid inline_728 := by
  rw [eq_inline_728]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 3) valid_5
  subst c
  exact placed_valid 1 (2, 4) valid_35

theorem eq_inline_729 : inline_729 = combine (6, 7) [inline_728, placed 2 (5, 10) card_460, placed 0 (2, 2) card_488] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_729 : Valid inline_729 := by
  rw [eq_inline_729]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_728
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 10) valid_460
  subst c
  exact placed_valid 0 (2, 2) valid_488

theorem eq_inline_730 : inline_730 = combine (6, 5) [placed 1 (2, 4) card_39, placed 1 (2, 4) card_80, inline_729] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_730 : Valid inline_730 := by
  rw [eq_inline_730]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_80
  subst c
  exact valid_inline_729

theorem eq_inline_731 : inline_731 = combine (4, 5) [placed 0 (3, 4) card_21, placed 7 (6, 7) card_56, inline_730] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_731 : Valid inline_731 := by
  rw [eq_inline_731]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_56
  subst c
  exact valid_inline_730

theorem eq_inline_732 : inline_732 = combine (3, 7) [placed 4 (3, 3) card_6, placed 1 (2, 4) card_8, placed 1 (0, 2) card_690, inline_731] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_732 : Valid inline_732 := by
  rw [eq_inline_732]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_690
  subst c
  exact valid_inline_731

theorem eq_card_691 : card_691 = combine (3, 6) [placed 1 (2, 3) card_8, inline_722, inline_727, inline_732] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_691 : Valid card_691 := by
  rw [eq_card_691]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact valid_inline_722
  rcases hc with rfl | hc
  · exact valid_inline_727
  subst c
  exact valid_inline_732


end OAI.Snaky21.Certificate

theorem solution : Valid card_688 ∧ Valid card_689 ∧ Valid card_690 ∧ Valid card_691 ∧ True :=
  ⟨valid_688, valid_689, valid_690, valid_691, True.intro⟩
