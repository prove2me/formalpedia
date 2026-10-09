-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block10_part00_group01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:00:57.060291+00:00
-- url     : https://prove2.me/submissions/2cef84c1-d7da-4cdb-a783-2cb1b7a37955

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_group00_valid
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
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_65 : Valid card_65 := block01_valid.2.1
theorem valid_72 : Valid card_72 := block01_valid.2.2.2.2.2.2.2.2.1
theorem valid_104 : Valid card_104 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_120 : Valid card_120 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_128 : Valid card_128 := block02_valid.1
theorem valid_144 : Valid card_144 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_262 : Valid card_262 := block04_valid.2.2.2.2.2.2.1
theorem valid_276 : Valid card_276 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_282 : Valid card_282 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_317 : Valid card_317 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_338 : Valid card_338 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_359 : Valid card_359 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_361 : Valid card_361 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_399 : Valid card_399 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_408 : Valid card_408 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_410 : Valid card_410 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_411 : Valid card_411 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_437 : Valid card_437 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_438 : Valid card_438 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_452 : Valid card_452 := block07_valid.2.2.2.2.1
theorem valid_476 : Valid card_476 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_479 : Valid card_479 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_480 : Valid card_480 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_546 : Valid card_546 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_587 : Valid card_587 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_600 : Valid card_600 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_611 : Valid card_611 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_613 : Valid card_613 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_621 : Valid card_621 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_634 : Valid card_634 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_635 : Valid card_635 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid_640 : Valid card_640 := block10_part00_group00_valid.1
theorem valid_642 : Valid card_642 := block10_part00_group00_valid.2.2.1
theorem valid_643 : Valid card_643 := block10_part00_group00_valid.2.2.2.1

theorem eq_inline_593 : inline_593 = combine (5, 5) [placed 3 (7, 4) card_10, placed 0 (3, 1) card_317, placed 2 (2, 8) card_640] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_593 : Valid inline_593 := by
  rw [eq_inline_593]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_317
  subst c
  exact placed_valid 2 (2, 8) valid_640

theorem eq_inline_594 : inline_594 = combine (6, 5) [placed 1 (1, 4) card_104, placed 1 (1, 4) card_359, placed 0 (1, 1) card_452, placed 2 (3, 8) card_476, placed 0 (3, 1) card_479, inline_593] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_594 : Valid inline_594 := by
  rw [eq_inline_594]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_104
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_359
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_476
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_479
  subst c
  exact valid_inline_593

theorem eq_card_644 : card_644 = combine (6, 4) [placed 6 (7, 7) card_120, placed 5 (1, 6) card_338, placed 5 (1, 7) card_437, placed 5 (0, 6) card_611, placed 1 (1, 3) card_613, placed 0 (1, 0) card_634, inline_594, placed 0 (3, 0) card_642, placed 0 (3, 0) card_643] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_644 : Valid card_644 := by
  rw [eq_card_644]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 7) valid_120
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_338
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_437
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_611
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_613
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_634
  rcases hc with rfl | hc
  · exact valid_inline_594
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_642
  subst c
  exact placed_valid 0 (3, 0) valid_643

theorem eq_inline_595 : inline_595 = combine (5, 4) [placed 3 (7, 4) card_44, placed 3 (7, 4) card_52, placed 5 (2, 5) card_128, placed 6 (6, 6) card_144] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_595 : Valid inline_595 := by
  rw [eq_inline_595]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_128
  subst c
  exact placed_valid 6 (6, 6) valid_144

theorem eq_inline_596 : inline_596 = combine (6, 5) [placed 1 (1, 4) card_104, placed 1 (1, 4) card_359, placed 2 (1, 8) card_438, placed 0 (1, 1) card_452, placed 2 (3, 8) card_476, placed 0 (3, 1) card_479] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_596 : Valid inline_596 := by
  rw [eq_inline_596]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_104
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_359
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_438
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_476
  subst c
  exact placed_valid 0 (3, 1) valid_479

theorem eq_card_645 : card_645 = combine (6, 4) [placed 6 (7, 7) card_120, placed 5 (1, 6) card_276, placed 5 (1, 6) card_338, placed 5 (1, 7) card_437, placed 5 (0, 6) card_611, placed 0 (1, 0) card_634, placed 0 (3, 0) card_642, placed 0 (3, 0) card_643, inline_595, inline_596] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_645 : Valid card_645 := by
  rw [eq_card_645]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 7) valid_120
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_276
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_338
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_437
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_611
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_634
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_642
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_643
  rcases hc with rfl | hc
  · exact valid_inline_595
  subst c
  exact valid_inline_596

theorem eq_inline_597 : inline_597 = combine (4, 2) [placed 4 (4, 1) card_15, placed 1 (2, 2) card_72, placed 7 (6, 5) card_262] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_597 : Valid inline_597 := by
  rw [eq_inline_597]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_72
  subst c
  exact placed_valid 7 (6, 5) valid_262

theorem eq_card_646 : card_646 = combine (4, 4) [placed 0 (1, 1) card_361, placed 3 (6, 1) card_361, placed 1 (0, 3) card_411, placed 3 (7, 1) card_600, placed 5 (0, 7) card_621, inline_597] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_646 : Valid card_646 := by
  rw [eq_card_646]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_361
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 1) valid_361
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_411
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 1) valid_600
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_621
  subst c
  exact valid_inline_597

theorem eq_inline_598 : inline_598 = combine (6, 5) [placed 7 (7, 5) card_15, placed 3 (8, 4) card_65, placed 6 (6, 7) card_282] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_598 : Valid inline_598 := by
  rw [eq_inline_598]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_65
  subst c
  exact placed_valid 6 (6, 7) valid_282

theorem eq_inline_599 : inline_599 = combine (5, 5) [placed 3 (8, 2) card_600, placed 2 (2, 8) card_600, placed 1 (1, 1) card_621, inline_598] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_599 : Valid inline_599 := by
  rw [eq_inline_599]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 2) valid_600
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_600
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_621
  subst c
  exact valid_inline_598

theorem eq_card_647 : card_647 = combine (5, 4) [placed 7 (8, 6) card_399, placed 5 (1, 5) card_408, placed 5 (1, 5) card_410, placed 3 (9, 1) card_480, placed 1 (0, 3) card_546, placed 5 (1, 6) card_587, placed 7 (9, 6) card_635, placed 1 (1, 1) card_646, inline_599] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_647 : Valid card_647 := by
  rw [eq_card_647]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_399
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_408
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_410
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 1) valid_480
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_546
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 6) valid_635
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_646
  subst c
  exact valid_inline_599


end OAI.Snaky21.Certificate

theorem solution : Valid card_644 ∧ Valid card_645 ∧ Valid card_646 ∧ Valid card_647 ∧ True :=
  ⟨valid_644, valid_645, valid_646, valid_647, True.intro⟩
