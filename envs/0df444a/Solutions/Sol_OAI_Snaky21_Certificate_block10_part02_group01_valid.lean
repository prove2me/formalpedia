-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part02_group01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:34:03.069082+00:00
-- url     : https://prove2.me/submissions/2f5ab3c2-8a2e-4563-8910-9753fd15c38c

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part02_group00_valid
import Definitions.Def_Snaky21Data10
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_valid
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
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_18 : Valid card_18 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_31 : Valid card_31 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_33 : Valid card_33 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_55 : Valid card_55 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_160 : Valid card_160 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_222 : Valid card_222 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_380 : Valid card_380 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_382 : Valid card_382 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_589 : Valid card_589 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem eq_inline_687 : inline_687 = combine (2, 4) [placed 6 (4, 6) card_55, placed 0 (1, 2) card_380] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_687 : Valid inline_687 := by
  rw [eq_inline_687]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_55
  subst c
  exact placed_valid 0 (1, 2) valid_380

theorem eq_card_676 : card_676 = combine (4, 3) [placed 5 (0, 3) card_7, placed 0 (1, 2) card_8, placed 1 (0, 2) card_9, inline_687] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_676 : Valid card_676 := by
  rw [eq_card_676]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_9
  subst c
  exact valid_inline_687

theorem eq_card_677 : card_677 = combine (3, 3) [placed 6 (4, 7) card_13, placed 2 (2, 7) card_14, placed 6 (4, 7) card_33, placed 5 (1, 6) card_589, placed 1 (0, 2) card_676] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_677 : Valid card_677 := by
  rw [eq_card_677]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_589
  subst c
  exact placed_valid 1 (0, 2) valid_676

theorem eq_inline_688 : inline_688 = combine (4, 3) [placed 7 (5, 4) card_22, placed 4 (4, 2) card_382] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_688 : Valid inline_688 := by
  rw [eq_inline_688]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_22
  subst c
  exact placed_valid 4 (4, 2) valid_382

theorem eq_inline_689 : inline_689 = combine (2, 6) [placed 6 (2, 6) card_18, inline_688] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_689 : Valid inline_689 := by
  rw [eq_inline_689]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_18
  subst c
  exact valid_inline_688

theorem eq_card_678 : card_678 = combine (1, 5) [placed 2 (0, 7) card_31, placed 5 (0, 5) card_160, inline_689] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_678 : Valid card_678 := by
  rw [eq_card_678]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_160
  subst c
  exact valid_inline_689

theorem eq_inline_690 : inline_690 = combine (3, 3) [placed 2 (0, 3) card_0, placed 3 (5, 1) card_222] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_690 : Valid inline_690 := by
  rw [eq_inline_690]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_0
  subst c
  exact placed_valid 3 (5, 1) valid_222

theorem eq_card_679 : card_679 = combine (2, 3) [placed 0 (1, 0) card_52, inline_690] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_679 : Valid card_679 := by
  rw [eq_card_679]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_52
  subst c
  exact valid_inline_690


end OAI.Snaky21.Certificate

theorem solution : Valid card_676 ∧ Valid card_677 ∧ Valid card_678 ∧ Valid card_679 ∧ True :=
  ⟨valid_676, valid_677, valid_678, valid_679, True.intro⟩
