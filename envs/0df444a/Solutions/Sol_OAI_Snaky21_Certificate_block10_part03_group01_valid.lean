-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part03_group01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:42:11.567983+00:00
-- url     : https://prove2.me/submissions/bbea68f0-ccb2-4d0e-ae00-eb1ce2632ed6

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
theorem valid_2 : Valid card_2 := block00_valid.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_17 : Valid card_17 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_26 : Valid card_26 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_28 : Valid card_28 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_67 : Valid card_67 := block01_valid.2.2.2.1
theorem valid_75 : Valid card_75 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_90 : Valid card_90 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_96 : Valid card_96 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_103 : Valid card_103 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_110 : Valid card_110 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_116 : Valid card_116 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_118 : Valid card_118 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_119 : Valid card_119 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_135 : Valid card_135 := block02_valid.2.2.2.2.2.2.2.1
theorem valid_142 : Valid card_142 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_147 : Valid card_147 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_168 : Valid card_168 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_175 : Valid card_175 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_182 : Valid card_182 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_188 : Valid card_188 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_192 : Valid card_192 := block03_valid.1
theorem valid_193 : Valid card_193 := block03_valid.2.1
theorem valid_214 : Valid card_214 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_228 : Valid card_228 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_233 : Valid card_233 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_308 : Valid card_308 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_314 : Valid card_314 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_319 : Valid card_319 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_324 : Valid card_324 := block05_valid.2.2.2.2.1
theorem valid_339 : Valid card_339 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_348 : Valid card_348 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_390 : Valid card_390 := block06_valid.2.2.2.2.2.2.1
theorem valid_396 : Valid card_396 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_397 : Valid card_397 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_399 : Valid card_399 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_409 : Valid card_409 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_430 : Valid card_430 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_461 : Valid card_461 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_475 : Valid card_475 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_509 : Valid card_509 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_544 : Valid card_544 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_545 : Valid card_545 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_546 : Valid card_546 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_549 : Valid card_549 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_611 : Valid card_611 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_686 : Valid card_686 := block10_part02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_688 : Valid card_688 := block10_part03_group00_valid.1
theorem valid_691 : Valid card_691 := block10_part03_group00_valid.2.2.2.1

theorem eq_inline_733 : inline_733 = combine (3, 3) [placed 2 (2, 7) card_13, placed 2 (2, 7) card_14, placed 5 (0, 6) card_118, placed 4 (4, 1) card_192, placed 0 (2, 1) card_193, placed 0 (1, 0) card_396, placed 7 (6, 6) card_435] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_733 : Valid inline_733 := by
  rw [eq_inline_733]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_193
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_396
  subst c
  exact placed_valid 7 (6, 6) valid_435

theorem eq_inline_734 : inline_734 = combine (4, 4) [placed 2 (0, 5) card_2, placed 2 (1, 7) card_509] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_734 : Valid inline_734 := by
  rw [eq_inline_734]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_2
  subst c
  exact placed_valid 2 (1, 7) valid_509

theorem eq_inline_735 : inline_735 = combine (3, 4) [placed 0 (0, 2) card_110, placed 0 (0, 2) card_119, placed 2 (1, 8) card_399, placed 0 (0, 1) card_430, placed 0 (0, 3) card_461, placed 2 (1, 8) card_475, inline_733, inline_734] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_735 : Valid inline_735 := by
  rw [eq_inline_735]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_110
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_119
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_399
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_430
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_461
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_475
  rcases hc with rfl | hc
  · exact valid_inline_733
  subst c
  exact valid_inline_734

theorem eq_card_692 : card_692 = combine (1, 5) [placed 1 (0, 2) card_5, inline_735] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_692 : Valid card_692 := by
  rw [eq_card_692]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_5
  subst c
  exact valid_inline_735

theorem eq_inline_736 : inline_736 = combine (5, 8) [placed 0 (4, 4) card_28, placed 1 (2, 7) card_409] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_736 : Valid inline_736 := by
  rw [eq_inline_736]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_28
  subst c
  exact placed_valid 1 (2, 7) valid_409

theorem eq_inline_737 : inline_737 = combine (5, 8) [placed 3 (7, 4) card_168, placed 1 (2, 7) card_409, placed 1 (1, 6) card_611] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_737 : Valid inline_737 := by
  rw [eq_inline_737]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_168
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 7) valid_409
  subst c
  exact placed_valid 1 (1, 6) valid_611

theorem eq_inline_738 : inline_738 = combine (5, 4) [placed 3 (6, 4) card_10, placed 2 (4, 8) card_308] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_738 : Valid inline_738 := by
  rw [eq_inline_738]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_10
  subst c
  exact placed_valid 2 (4, 8) valid_308

theorem eq_inline_739 : inline_739 = combine (3, 5) [placed 3 (7, 5) card_6, placed 4 (6, 4) card_26, placed 4 (7, 2) card_214, inline_738] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_739 : Valid inline_739 := by
  rw [eq_inline_739]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 4) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_214
  subst c
  exact valid_inline_738

theorem eq_inline_740 : inline_740 = combine (5, 4) [placed 4 (7, 4) card_233, placed 7 (6, 7) card_314, placed 5 (4, 7) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_740 : Valid inline_740 := by
  rw [eq_inline_740]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 4) valid_233
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_314
  subst c
  exact placed_valid 5 (4, 7) valid_314

theorem eq_inline_741 : inline_741 = combine (5, 6) [placed 6 (5, 8) card_44, placed 2 (5, 8) card_52, inline_740] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_741 : Valid inline_741 := by
  rw [eq_inline_741]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_52
  subst c
  exact valid_inline_740

theorem eq_inline_742 : inline_742 = combine (5, 7) [placed 6 (7, 10) card_319, inline_736, inline_737, inline_739, inline_741] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_742 : Valid inline_742 := by
  rw [eq_inline_742]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 10) valid_319
  rcases hc with rfl | hc
  · exact valid_inline_736
  rcases hc with rfl | hc
  · exact valid_inline_737
  rcases hc with rfl | hc
  · exact valid_inline_739
  subst c
  exact valid_inline_741

theorem eq_card_693 : card_693 = combine (7, 8) [placed 0 (4, 4) card_147, placed 7 (8, 8) card_339, placed 1 (2, 5) card_692, inline_742] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_693 : Valid card_693 := by
  rw [eq_card_693]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_147
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 8) valid_339
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_692
  subst c
  exact valid_inline_742

theorem eq_inline_743 : inline_743 = combine (4, 6) [placed 2 (4, 11) card_390, placed 4 (7, 3) card_544, placed 1 (0, 5) card_545, placed 3 (9, 5) card_546, placed 1 (0, 5) card_549] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_743 : Valid inline_743 := by
  rw [eq_inline_743]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 11) valid_390
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_544
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 5) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 5) valid_546
  subst c
  exact placed_valid 1 (0, 5) valid_549

theorem eq_inline_744 : inline_744 = combine (5, 4) [placed 2 (5, 8) card_7, placed 5 (4, 7) card_26, placed 7 (8, 8) card_142, placed 5 (0, 11) card_693] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_744 : Valid inline_744 := by
  rw [eq_inline_744]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 7) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 8) valid_142
  subst c
  exact placed_valid 5 (0, 11) valid_693

theorem eq_card_694 : card_694 = combine (5, 7) [placed 5 (2, 8) card_116, placed 4 (7, 3) card_188, placed 1 (2, 5) card_397, placed 3 (8, 4) card_435, placed 0 (2, 2) card_691, inline_743, inline_744] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_694 : Valid card_694 := by
  rw [eq_card_694]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_397
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_691
  rcases hc with rfl | hc
  · exact valid_inline_743
  subst c
  exact valid_inline_744

theorem eq_inline_745 : inline_745 = combine (1, 6) [placed 0 (1, 3) card_11, placed 4 (2, 2) card_75, placed 2 (1, 7) card_103] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_745 : Valid inline_745 := by
  rw [eq_inline_745]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_75
  subst c
  exact placed_valid 2 (1, 7) valid_103

theorem eq_inline_746 : inline_746 = combine (1, 6) [placed 0 (1, 3) card_11, placed 4 (2, 4) card_17, placed 7 (2, 7) card_90] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_746 : Valid inline_746 := by
  rw [eq_inline_746]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 4) valid_17
  subst c
  exact placed_valid 7 (2, 7) valid_90

theorem eq_inline_747 : inline_747 = combine (1, 7) [placed 6 (2, 8) card_308, placed 3 (5, 5) card_348, inline_745, inline_746] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_747 : Valid inline_747 := by
  rw [eq_inline_747]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 8) valid_308
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 5) valid_348
  rcases hc with rfl | hc
  · exact valid_inline_745
  subst c
  exact valid_inline_746

theorem eq_inline_748 : inline_748 = combine (1, 4) [placed 6 (4, 5) card_5, inline_747] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_748 : Valid inline_748 := by
  rw [eq_inline_748]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_5
  subst c
  exact valid_inline_747

theorem eq_inline_749 : inline_749 = combine (3, 8) [placed 0 (1, 4) card_96, inline_748] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_749 : Valid inline_749 := by
  rw [eq_inline_749]
  apply combination_rule (3, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_96
  subst c
  exact valid_inline_748

theorem eq_inline_750 : inline_750 = combine (1, 5) [placed 0 (1, 5) card_5, inline_749] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_750 : Valid inline_750 := by
  rw [eq_inline_750]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 5) valid_5
  subst c
  exact valid_inline_749

theorem eq_inline_751 : inline_751 = combine (4, 7) [placed 4 (5, 3) card_67, placed 6 (5, 9) card_175, placed 1 (1, 4) card_228, placed 3 (7, 4) card_435, placed 1 (0, 5) card_688, inline_750] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_751 : Valid inline_751 := by
  rw [eq_inline_751]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 9) valid_175
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_228
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 5) valid_688
  subst c
  exact valid_inline_750

theorem eq_inline_752 : inline_752 = combine (4, 6) [placed 1 (1, 5) card_44, placed 4 (5, 1) card_324, placed 0 (0, 2) card_686, inline_751] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_752 : Valid inline_752 := by
  rw [eq_inline_752]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 5) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_324
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_686
  subst c
  exact valid_inline_751

theorem eq_card_695 : card_695 = combine (4, 5) [placed 1 (0, 4) card_12, placed 2 (1, 8) card_118, placed 1 (0, 3) card_135, placed 5 (0, 7) card_182, inline_752] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_695 : Valid card_695 := by
  rw [eq_card_695]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_182
  subst c
  exact valid_inline_752


end OAI.Snaky21.Certificate

theorem solution : Valid card_692 ∧ Valid card_693 ∧ Valid card_694 ∧ Valid card_695 ∧ True :=
  ⟨valid_692, valid_693, valid_694, valid_695, True.intro⟩
