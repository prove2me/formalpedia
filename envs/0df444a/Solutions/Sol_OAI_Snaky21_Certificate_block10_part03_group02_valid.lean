-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part03_group02_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:46:59.350207+00:00
-- url     : https://prove2.me/submissions/082f9c5b-5e8a-456c-8c04-c2a1329cafd3

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part03_group00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part03_group01_valid
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
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_16 : Valid card_16 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_21 : Valid card_21 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_39 : Valid card_39 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_42 : Valid card_42 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_48 : Valid card_48 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_95 : Valid card_95 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_112 : Valid card_112 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_121 : Valid card_121 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_134 : Valid card_134 := block02_valid.2.2.2.2.2.2.1
theorem valid_147 : Valid card_147 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_151 : Valid card_151 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_182 : Valid card_182 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_188 : Valid card_188 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_197 : Valid card_197 := block03_valid.2.2.2.2.2.1
theorem valid_249 : Valid card_249 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_259 : Valid card_259 := block04_valid.2.2.2.1
theorem valid_317 : Valid card_317 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_321 : Valid card_321 := block05_valid.2.1
theorem valid_322 : Valid card_322 := block05_valid.2.2.1
theorem valid_369 : Valid card_369 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_371 : Valid card_371 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_374 : Valid card_374 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_389 : Valid card_389 := block06_valid.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_436 : Valid card_436 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_460 : Valid card_460 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_545 : Valid card_545 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_546 : Valid card_546 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_549 : Valid card_549 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_619 : Valid card_619 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_620 : Valid card_620 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_622 : Valid card_622 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_685 : Valid card_685 := block10_part02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_687 : Valid card_687 := block10_part02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_690 : Valid card_690 := block10_part03_group00_valid.2.2.1
theorem valid_692 : Valid card_692 := block10_part03_group01_valid.1
theorem valid_693 : Valid card_693 := block10_part03_group01_valid.2.1

theorem eq_inline_753 : inline_753 = combine (5, 7) [placed 7 (5, 7) card_5, placed 3 (6, 4) card_197] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_753 : Valid inline_753 := by
  rw [eq_inline_753]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 7) valid_5
  subst c
  exact placed_valid 3 (6, 4) valid_197

theorem eq_inline_754 : inline_754 = combine (4, 4) [placed 5 (1, 7) card_317, inline_753, placed 7 (8, 7) card_436, placed 6 (8, 9) card_685] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_754 : Valid inline_754 := by
  rw [eq_inline_754]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_317
  rcases hc with rfl | hc
  · exact valid_inline_753
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_436
  subst c
  exact placed_valid 6 (8, 9) valid_685

theorem eq_card_696 : card_696 = combine (5, 4) [placed 6 (6, 8) card_12, placed 7 (9, 7) card_322, placed 4 (6, 1) card_369, placed 7 (8, 7) card_435, placed 0 (2, 1) card_622, inline_754] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_696 : Valid card_696 := by
  rw [eq_card_696]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 7) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_622
  subst c
  exact valid_inline_754

theorem eq_inline_755 : inline_755 = combine (5, 2) [placed 7 (5, 3) card_16, placed 0 (2, 2) card_374] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_755 : Valid inline_755 := by
  rw [eq_inline_755]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 3) valid_16
  subst c
  exact placed_valid 0 (2, 2) valid_374

theorem eq_inline_756 : inline_756 = combine (6, 6) [placed 7 (9, 7) card_95, inline_755] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_756 : Valid inline_756 := by
  rw [eq_inline_756]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 7) valid_95
  subst c
  exact valid_inline_755

theorem eq_inline_757 : inline_757 = combine (5, 6) [placed 7 (6, 6) card_151, placed 3 (8, 5) card_460, inline_756] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_757 : Valid inline_757 := by
  rw [eq_inline_757]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_151
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_460
  subst c
  exact valid_inline_756

theorem eq_inline_758 : inline_758 = combine (3, 6) [placed 4 (4, 2) card_39, placed 4 (5, 2) card_121, inline_757] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_758 : Valid inline_758 := by
  rw [eq_inline_758]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_121
  subst c
  exact valid_inline_757

theorem eq_inline_759 : inline_759 = combine (3, 4) [placed 1 (2, 3) card_21, placed 6 (5, 6) card_56, inline_758] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_759 : Valid inline_759 := by
  rw [eq_inline_759]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_56
  subst c
  exact valid_inline_758

theorem eq_card_697 : card_697 = combine (5, 3) [placed 7 (6, 3) card_7, placed 0 (2, 2) card_8, placed 0 (0, 0) card_690, inline_759] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_697 : Valid card_697 := by
  rw [eq_card_697]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_690
  subst c
  exact valid_inline_759

theorem eq_card_698 : card_698 = combine (4, 6) [placed 0 (3, 2) card_12, placed 6 (6, 8) card_182, placed 0 (2, 2) card_188, placed 3 (7, 3) card_619, placed 0 (1, 0) card_620, placed 0 (1, 1) card_622, placed 1 (0, 1) card_687, placed 1 (1, 2) card_697] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_698 : Valid card_698 := by
  rw [eq_card_698]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_182
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_619
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_620
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_622
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_687
  subst c
  exact placed_valid 1 (1, 2) valid_697

theorem eq_inline_760 : inline_760 = combine (7, 6) [placed 0 (6, 4) card_42, placed 1 (4, 5) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_760 : Valid inline_760 := by
  rw [eq_inline_760]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 4) valid_42
  subst c
  exact placed_valid 1 (4, 5) valid_52

theorem eq_inline_761 : inline_761 = combine (7, 8) [placed 7 (10, 9) card_95, placed 1 (4, 4) card_112, inline_760] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_761 : Valid inline_761 := by
  rw [eq_inline_761]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 9) valid_95
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_112
  subst c
  exact valid_inline_760

theorem eq_inline_762 : inline_762 = combine (6, 8) [placed 0 (4, 4) card_371, placed 3 (9, 7) card_460, inline_761] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_762 : Valid inline_762 := by
  rw [eq_inline_762]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_371
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 7) valid_460
  subst c
  exact valid_inline_761

theorem eq_inline_763 : inline_763 = combine (4, 8) [placed 4 (7, 4) card_147, placed 5 (3, 8) card_249, placed 3 (9, 5) card_692, inline_762] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_763 : Valid inline_763 := by
  rw [eq_inline_763]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 4) valid_147
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_249
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 5) valid_692
  subst c
  exact valid_inline_762

theorem eq_inline_764 : inline_764 = combine (7, 4) [placed 2 (4, 5) card_5, placed 2 (5, 7) card_259] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_764 : Valid inline_764 := by
  rw [eq_inline_764]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 5) valid_5
  subst c
  exact placed_valid 2 (5, 7) valid_259

theorem eq_inline_765 : inline_765 = combine (6, 3) [placed 6 (7, 6) card_10, placed 6 (7, 6) card_48, placed 5 (4, 6) card_134, inline_764] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_765 : Valid inline_765 := by
  rw [eq_inline_765]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_48
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_134
  subst c
  exact valid_inline_764

theorem eq_inline_766 : inline_766 = combine (6, 4) [placed 5 (4, 5) card_389, placed 0 (5, 0) card_545, placed 2 (5, 9) card_546, placed 0 (5, 0) card_549, inline_765] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_766 : Valid inline_766 := by
  rw [eq_inline_766]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 5) valid_389
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 0) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 9) valid_546
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 0) valid_549
  subst c
  exact valid_inline_765

theorem eq_card_699 : card_699 = combine (7, 5) [placed 0 (4, 4) card_197, placed 0 (4, 1) card_321, placed 4 (11, 0) card_693, inline_763, inline_766] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_699 : Valid card_699 := by
  rw [eq_card_699]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_321
  rcases hc with rfl | hc
  · exact placed_valid 4 (11, 0) valid_693
  rcases hc with rfl | hc
  · exact valid_inline_763
  subst c
  exact valid_inline_766


end OAI.Snaky21.Certificate

theorem solution : Valid card_696 ∧ Valid card_697 ∧ Valid card_698 ∧ Valid card_699 ∧ True :=
  ⟨valid_696, valid_697, valid_698, valid_699, True.intro⟩
