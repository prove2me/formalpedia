-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block00_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T08:00:36.126152+00:00
-- url     : https://prove2.me/submissions/eb773161-5f90-4acf-84fc-54af923e4ae2

import Definitions.Def_Snaky21Data00
import Theorems.Thm_OAI_Snaky21_claim_calculus
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
namespace OAI.Snaky21
theorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i
theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h
end OAI.Snaky21
namespace OAI.Snaky21.Certificate
end OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl

theorem valid_0 : Valid card_0 := base_valid 0

theorem valid_1 : Valid card_1 := base_valid 1

theorem valid_2 : Valid card_2 := base_valid 2

theorem valid_3 : Valid card_3 := base_valid 3

theorem valid_4 : Valid card_4 := base_valid 4

theorem valid_5 : Valid card_5 := base_valid 5

theorem eq_card_6 : card_6 = combine (1, 4) [placed 1 (0, 0) card_4, placed 1 (0, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_6 : Valid card_6 := by
  rw [eq_card_6]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_4
  subst c
  exact placed_valid 1 (0, 1) valid_5

theorem eq_card_7 : card_7 = combine (0, 5) [placed 0 (0, 1) card_6, placed 2 (0, 5) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_7 : Valid card_7 := by
  rw [eq_card_7]
  apply combination_rule (0, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_6
  subst c
  exact placed_valid 2 (0, 5) valid_6

theorem eq_card_8 : card_8 = combine (4, 1) [placed 1 (0, 1) card_6, placed 5 (0, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_8 : Valid card_8 := by
  rw [eq_card_8]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_6
  subst c
  exact placed_valid 5 (0, 1) valid_6

theorem eq_card_9 : card_9 = combine (1, 5) [placed 0 (1, 1) card_6, placed 6 (1, 5) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_9 : Valid card_9 := by
  rw [eq_card_9]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_6
  subst c
  exact placed_valid 6 (1, 5) valid_6

theorem eq_card_10 : card_10 = combine (1, 4) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_8] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_10 : Valid card_10 := by
  rw [eq_card_10]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_8

theorem eq_card_11 : card_11 = combine (1, 1) [placed 5 (0, 5) card_0, placed 5 (0, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_11 : Valid card_11 := by
  rw [eq_card_11]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_0
  subst c
  exact placed_valid 5 (0, 4) valid_5

theorem eq_card_12 : card_12 = combine (1, 5) [placed 6 (1, 6) card_7, placed 1 (0, 2) card_8, placed 6 (2, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_12 : Valid card_12 := by
  rw [eq_card_12]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  subst c
  exact placed_valid 6 (2, 6) valid_9

theorem eq_card_13 : card_13 = combine (1, 5) [placed 4 (1, 1) card_7, placed 1 (0, 2) card_8, placed 6 (2, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_13 : Valid card_13 := by
  rw [eq_card_13]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 1) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  subst c
  exact placed_valid 6 (2, 6) valid_9

theorem eq_card_14 : card_14 = combine (1, 5) [placed 6 (1, 6) card_7, placed 1 (0, 2) card_8, placed 0 (0, 1) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_14 : Valid card_14 := by
  rw [eq_card_14]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  subst c
  exact placed_valid 0 (0, 1) valid_9

theorem eq_card_15 : card_15 = combine (1, 4) [placed 1 (0, 0) card_0, placed 7 (1, 5) card_0] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_15 : Valid card_15 := by
  rw [eq_card_15]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 7 (1, 5) valid_0

theorem eq_card_16 : card_16 = combine (0, 4) [placed 5 (0, 4) card_4, placed 0 (0, 0) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_16 : Valid card_16 := by
  rw [eq_card_16]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_4
  subst c
  exact placed_valid 0 (0, 0) valid_6

theorem eq_card_17 : card_17 = combine (1, 4) [placed 0 (1, 0) card_6, placed 4 (1, 1) card_16] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_17 : Valid card_17 := by
  rw [eq_card_17]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_6
  subst c
  exact placed_valid 4 (1, 1) valid_16

theorem eq_card_18 : card_18 = combine (1, 4) [placed 7 (1, 4) card_4, placed 1 (0, 1) card_8] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_18 : Valid card_18 := by
  rw [eq_card_18]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 1 (0, 1) valid_8

theorem eq_card_19 : card_19 = combine (0, 1) [placed 7 (1, 4) card_5, placed 0 (0, 1) card_18] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_19 : Valid card_19 := by
  rw [eq_card_19]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_18

theorem eq_card_20 : card_20 = combine (1, 4) [placed 7 (1, 5) card_0, placed 0 (1, 0) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_20 : Valid card_20 := by
  rw [eq_card_20]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 0 (1, 0) valid_6

theorem eq_card_21 : card_21 = combine (0, 4) [placed 5 (0, 4) card_5, placed 0 (0, 0) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_21 : Valid card_21 := by
  rw [eq_card_21]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_6

theorem eq_card_22 : card_22 = combine (0, 3) [placed 5 (0, 5) card_0, placed 5 (0, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_22 : Valid card_22 := by
  rw [eq_card_22]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_0
  subst c
  exact placed_valid 5 (0, 4) valid_5

theorem eq_card_23 : card_23 = combine (0, 4) [placed 5 (0, 5) card_0, placed 5 (0, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_23 : Valid card_23 := by
  rw [eq_card_23]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_0
  subst c
  exact placed_valid 5 (0, 4) valid_5

theorem eq_card_24 : card_24 = combine (4, 1) [placed 6 (4, 1) card_4, placed 1 (0, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_24 : Valid card_24 := by
  rw [eq_card_24]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 1) valid_4
  subst c
  exact placed_valid 1 (0, 1) valid_6

theorem eq_card_25 : card_25 = combine (3, 0) [placed 5 (2, 4) card_2, placed 2 (0, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_25 : Valid card_25 := by
  rw [eq_card_25]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_2
  subst c
  exact placed_valid 2 (0, 1) valid_5

theorem eq_card_26 : card_26 = combine (4, 1) [placed 1 (0, 1) card_6, placed 5 (0, 1) card_7] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_26 : Valid card_26 := by
  rw [eq_card_26]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_6
  subst c
  exact placed_valid 5 (0, 1) valid_7

theorem eq_card_27 : card_27 = combine (0, 4) [placed 5 (0, 4) card_5, placed 0 (0, 1) card_16] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_27 : Valid card_27 := by
  rw [eq_card_27]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_16

theorem eq_card_28 : card_28 = combine (1, 2) [placed 5 (1, 4) card_5, placed 7 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_28 : Valid card_28 := by
  rw [eq_card_28]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 7 (1, 4) valid_5

theorem eq_card_29 : card_29 = combine (0, 4) [placed 5 (0, 5) card_0, placed 0 (0, 0) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_29 : Valid card_29 := by
  rw [eq_card_29]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_6

theorem eq_card_30 : card_30 = combine (0, 2) [placed 5 (0, 4) card_0, placed 1 (0, 0) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_30 : Valid card_30 := by
  rw [eq_card_30]
  apply combination_rule (0, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_0
  subst c
  exact placed_valid 1 (0, 0) valid_5

theorem eq_card_31 : card_31 = combine (1, 5) [placed 1 (0, 2) card_8, placed 5 (0, 5) card_8] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_31 : Valid card_31 := by
  rw [eq_card_31]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  subst c
  exact placed_valid 5 (0, 5) valid_8

theorem eq_card_32 : card_32 = combine (3, 0) [placed 5 (2, 4) card_0, placed 2 (0, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_32 : Valid card_32 := by
  rw [eq_card_32]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_0
  subst c
  exact placed_valid 2 (0, 1) valid_5

theorem eq_card_33 : card_33 = combine (1, 5) [placed 4 (1, 1) card_7, placed 5 (0, 5) card_8, placed 4 (2, 1) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_33 : Valid card_33 := by
  rw [eq_card_33]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 1) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_8
  subst c
  exact placed_valid 4 (2, 1) valid_9

theorem eq_card_34 : card_34 = combine (0, 3) [placed 1 (0, 1) card_5, placed 5 (0, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_34 : Valid card_34 := by
  rw [eq_card_34]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_5

theorem eq_card_35 : card_35 = combine (3, 2) [placed 7 (3, 4) card_1, placed 0 (0, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_35 : Valid card_35 := by
  rw [eq_card_35]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_1
  subst c
  exact placed_valid 0 (0, 1) valid_5

theorem eq_card_36 : card_36 = combine (1, 4) [placed 1 (0, 0) card_2, placed 7 (1, 4) card_2] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_36 : Valid card_36 := by
  rw [eq_card_36]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_2
  subst c
  exact placed_valid 7 (1, 4) valid_2

theorem eq_card_37 : card_37 = combine (1, 4) [placed 7 (1, 4) card_5, placed 0 (1, 0) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_37 : Valid card_37 := by
  rw [eq_card_37]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_6

theorem eq_card_38 : card_38 = combine (3, 2) [placed 7 (3, 4) card_0, placed 0 (0, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_38 : Valid card_38 := by
  rw [eq_card_38]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_5

theorem eq_card_39 : card_39 = combine (1, 3) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_8] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_39 : Valid card_39 := by
  rw [eq_card_39]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_8

theorem eq_card_40 : card_40 = combine (1, 3) [placed 1 (1, 1) card_5, placed 7 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_40 : Valid card_40 := by
  rw [eq_card_40]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact placed_valid 7 (1, 4) valid_5

theorem eq_card_41 : card_41 = combine (1, 4) [placed 4 (1, 0) card_6, placed 1 (0, 1) card_24] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_41 : Valid card_41 := by
  rw [eq_card_41]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_6
  subst c
  exact placed_valid 1 (0, 1) valid_24

theorem eq_card_42 : card_42 = combine (1, 3) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_24] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_42 : Valid card_42 := by
  rw [eq_card_42]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_24

theorem eq_card_43 : card_43 = combine (1, 4) [placed 7 (1, 5) card_0, placed 7 (1, 4) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_43 : Valid card_43 := by
  rw [eq_card_43]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 7 (1, 4) valid_3

theorem eq_card_44 : card_44 = combine (1, 4) [placed 1 (0, 0) card_0, placed 0 (0, 1) card_43] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_44 : Valid card_44 := by
  rw [eq_card_44]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_43

theorem eq_card_45 : card_45 = combine (3, 3) [placed 0 (0, 2) card_5, placed 4 (3, 0) card_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_45 : Valid card_45 := by
  rw [eq_card_45]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_23

theorem eq_card_46 : card_46 = combine (3, 1) [placed 2 (0, 2) card_5, placed 0 (0, 0) card_45] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_46 : Valid card_46 := by
  rw [eq_card_46]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_45

theorem eq_card_47 : card_47 = combine (4, 2) [placed 1 (0, 2) card_7, placed 5 (0, 3) card_9, placed 0 (1, 0) card_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_47 : Valid card_47 := by
  rw [eq_card_47]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_9
  subst c
  exact placed_valid 0 (1, 0) valid_46

theorem eq_card_48 : card_48 = combine (1, 4) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_24] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_48 : Valid card_48 := by
  rw [eq_card_48]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_24

theorem eq_card_49 : card_49 = combine (4, 1) [placed 5 (0, 1) card_6, placed 1 (0, 0) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_49 : Valid card_49 := by
  rw [eq_card_49]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_6
  subst c
  exact placed_valid 1 (0, 0) valid_9

theorem eq_card_50 : card_50 = combine (1, 2) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_8] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_50 : Valid card_50 := by
  rw [eq_card_50]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_8

theorem eq_card_51 : card_51 = combine (1, 4) [placed 7 (1, 5) card_0, placed 1 (0, 0) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_51 : Valid card_51 := by
  rw [eq_card_51]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 1 (0, 0) valid_3

theorem eq_card_52 : card_52 = combine (1, 4) [placed 1 (0, 0) card_0, placed 0 (0, 1) card_51] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_52 : Valid card_52 := by
  rw [eq_card_52]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_51

theorem eq_card_53 : card_53 = combine (0, 1) [placed 1 (0, 0) card_0, placed 0 (0, 1) card_51] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_53 : Valid card_53 := by
  rw [eq_card_53]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_51

theorem eq_card_54 : card_54 = combine (0, 2) [placed 1 (0, 0) card_0, placed 0 (0, 1) card_51] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_54 : Valid card_54 := by
  rw [eq_card_54]
  apply combination_rule (0, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_51

theorem eq_card_55 : card_55 = combine (3, 4) [placed 0 (0, 3) card_5, placed 0 (2, 0) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_55 : Valid card_55 := by
  rw [eq_card_55]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_53

theorem eq_card_56 : card_56 = combine (3, 4) [placed 0 (0, 3) card_5, placed 6 (3, 6) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_56 : Valid card_56 := by
  rw [eq_card_56]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_5
  subst c
  exact placed_valid 6 (3, 6) valid_53

theorem eq_card_57 : card_57 = combine (3, 4) [placed 1 (0, 3) card_52, placed 6 (3, 6) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_57 : Valid card_57 := by
  rw [eq_card_57]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_52
  subst c
  exact placed_valid 6 (3, 6) valid_53

theorem eq_card_58 : card_58 = combine (4, 3) [placed 0 (0, 2) card_2, placed 0 (3, 0) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_58 : Valid card_58 := by
  rw [eq_card_58]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_2
  subst c
  exact placed_valid 0 (3, 0) valid_52

theorem eq_card_59 : card_59 = combine (3, 2) [placed 3 (4, 2) card_28, placed 0 (2, 0) card_31, placed 0 (0, 1) card_58] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_59 : Valid card_59 := by
  rw [eq_card_59]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 2) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_31
  subst c
  exact placed_valid 0 (0, 1) valid_58

theorem eq_card_60 : card_60 = combine (0, 3) [placed 4 (4, 2) card_0, placed 4 (1, 0) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_60 : Valid card_60 := by
  rw [eq_card_60]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_0
  subst c
  exact placed_valid 4 (1, 0) valid_52

theorem eq_card_61 : card_61 = combine (1, 3) [placed 1 (0, 0) card_0, placed 0 (0, 1) card_51] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_61 : Valid card_61 := by
  rw [eq_card_61]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_51

theorem eq_card_62 : card_62 = combine (1, 5) [placed 2 (1, 5) card_6, placed 6 (1, 5) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_62 : Valid card_62 := by
  rw [eq_card_62]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_6
  subst c
  exact placed_valid 6 (1, 5) valid_6

theorem eq_card_63 : card_63 = combine (1, 4) [placed 4 (1, 1) card_16, placed 1 (0, 1) card_24, placed 2 (0, 5) card_62] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_63 : Valid card_63 := by
  rw [eq_card_63]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 1) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_24
  subst c
  exact placed_valid 2 (0, 5) valid_62

theorem block00_valid : Valid card_0 ∧ Valid card_1 ∧ Valid card_2 ∧ Valid card_3 ∧ Valid card_4 ∧ Valid card_5 ∧ Valid card_6 ∧ Valid card_7 ∧ Valid card_8 ∧ Valid card_9 ∧ Valid card_10 ∧ Valid card_11 ∧ Valid card_12 ∧ Valid card_13 ∧ Valid card_14 ∧ Valid card_15 ∧ Valid card_16 ∧ Valid card_17 ∧ Valid card_18 ∧ Valid card_19 ∧ Valid card_20 ∧ Valid card_21 ∧ Valid card_22 ∧ Valid card_23 ∧ Valid card_24 ∧ Valid card_25 ∧ Valid card_26 ∧ Valid card_27 ∧ Valid card_28 ∧ Valid card_29 ∧ Valid card_30 ∧ Valid card_31 ∧ Valid card_32 ∧ Valid card_33 ∧ Valid card_34 ∧ Valid card_35 ∧ Valid card_36 ∧ Valid card_37 ∧ Valid card_38 ∧ Valid card_39 ∧ Valid card_40 ∧ Valid card_41 ∧ Valid card_42 ∧ Valid card_43 ∧ Valid card_44 ∧ Valid card_45 ∧ Valid card_46 ∧ Valid card_47 ∧ Valid card_48 ∧ Valid card_49 ∧ Valid card_50 ∧ Valid card_51 ∧ Valid card_52 ∧ Valid card_53 ∧ Valid card_54 ∧ Valid card_55 ∧ Valid card_56 ∧ Valid card_57 ∧ Valid card_58 ∧ Valid card_59 ∧ Valid card_60 ∧ Valid card_61 ∧ Valid card_62 ∧ Valid card_63 ∧ True :=
  ⟨valid_0, valid_1, valid_2, valid_3, valid_4, valid_5, valid_6, valid_7, valid_8, valid_9, valid_10, valid_11, valid_12, valid_13, valid_14, valid_15, valid_16, valid_17, valid_18, valid_19, valid_20, valid_21, valid_22, valid_23, valid_24, valid_25, valid_26, valid_27, valid_28, valid_29, valid_30, valid_31, valid_32, valid_33, valid_34, valid_35, valid_36, valid_37, valid_38, valid_39, valid_40, valid_41, valid_42, valid_43, valid_44, valid_45, valid_46, valid_47, valid_48, valid_49, valid_50, valid_51, valid_52, valid_53, valid_54, valid_55, valid_56, valid_57, valid_58, valid_59, valid_60, valid_61, valid_62, valid_63, True.intro⟩

end OAI.Snaky21.Certificate

theorem solution : Valid card_0 ∧ Valid card_1 ∧ Valid card_2 ∧ Valid card_3 ∧ Valid card_4 ∧ Valid card_5 ∧ Valid card_6 ∧ Valid card_7 ∧ Valid card_8 ∧ Valid card_9 ∧ Valid card_10 ∧ Valid card_11 ∧ Valid card_12 ∧ Valid card_13 ∧ Valid card_14 ∧ Valid card_15 ∧ Valid card_16 ∧ Valid card_17 ∧ Valid card_18 ∧ Valid card_19 ∧ Valid card_20 ∧ Valid card_21 ∧ Valid card_22 ∧ Valid card_23 ∧ Valid card_24 ∧ Valid card_25 ∧ Valid card_26 ∧ Valid card_27 ∧ Valid card_28 ∧ Valid card_29 ∧ Valid card_30 ∧ Valid card_31 ∧ Valid card_32 ∧ Valid card_33 ∧ Valid card_34 ∧ Valid card_35 ∧ Valid card_36 ∧ Valid card_37 ∧ Valid card_38 ∧ Valid card_39 ∧ Valid card_40 ∧ Valid card_41 ∧ Valid card_42 ∧ Valid card_43 ∧ Valid card_44 ∧ Valid card_45 ∧ Valid card_46 ∧ Valid card_47 ∧ Valid card_48 ∧ Valid card_49 ∧ Valid card_50 ∧ Valid card_51 ∧ Valid card_52 ∧ Valid card_53 ∧ Valid card_54 ∧ Valid card_55 ∧ Valid card_56 ∧ Valid card_57 ∧ Valid card_58 ∧ Valid card_59 ∧ Valid card_60 ∧ Valid card_61 ∧ Valid card_62 ∧ Valid card_63 ∧ True := block00_valid
