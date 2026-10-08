-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T08:18:48.417109+00:00
-- url     : https://prove2.me/submissions/b546d186-4e5a-4ebd-a2bc-4922196bb9cd

import Definitions.Def_Snaky21Data01
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
namespace OAI.Snaky21
theorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i
theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h
end OAI.Snaky21
namespace OAI.Snaky21.Certificate
theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl
end OAI.Snaky21.Certificate
namespace OAI.Snaky21.Certificate
theorem valid_0 : Valid card_0 := block00_valid.1
theorem valid_1 : Valid card_1 := block00_valid.2.1
theorem valid_2 : Valid card_2 := block00_valid.2.2.1
theorem valid_3 : Valid card_3 := block00_valid.2.2.2.1
theorem valid_4 : Valid card_4 := block00_valid.2.2.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_16 : Valid card_16 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_17 : Valid card_17 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_18 : Valid card_18 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_19 : Valid card_19 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_20 : Valid card_20 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_21 : Valid card_21 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_23 : Valid card_23 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_24 : Valid card_24 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_25 : Valid card_25 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_26 : Valid card_26 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_27 : Valid card_27 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_28 : Valid card_28 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_29 : Valid card_29 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_30 : Valid card_30 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_31 : Valid card_31 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_32 : Valid card_32 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_33 : Valid card_33 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_34 : Valid card_34 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_35 : Valid card_35 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_36 : Valid card_36 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_37 : Valid card_37 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_38 : Valid card_38 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_39 : Valid card_39 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_40 : Valid card_40 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_41 : Valid card_41 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_42 : Valid card_42 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_43 : Valid card_43 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_45 : Valid card_45 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_46 : Valid card_46 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_47 : Valid card_47 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_48 : Valid card_48 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_49 : Valid card_49 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_50 : Valid card_50 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_51 : Valid card_51 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_54 : Valid card_54 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_55 : Valid card_55 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_57 : Valid card_57 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_58 : Valid card_58 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_59 : Valid card_59 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_60 : Valid card_60 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_61 : Valid card_61 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_62 : Valid card_62 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_63 : Valid card_63 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
end OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_64 : card_64 = combine (0, 2) [placed 1 (0, 0) card_0, placed 0 (0, 1) card_43] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_64 : Valid card_64 := by
  rw [eq_card_64]
  apply combination_rule (0, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_43

theorem eq_card_65 : card_65 = combine (1, 5) [placed 0 (0, 2) card_20, placed 2 (0, 5) card_20] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_65 : Valid card_65 := by
  rw [eq_card_65]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_20
  subst c
  exact placed_valid 2 (0, 5) valid_20

theorem eq_card_66 : card_66 = combine (1, 4) [placed 7 (1, 5) card_0, placed 5 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_66 : Valid card_66 := by
  rw [eq_card_66]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 5 (1, 4) valid_5

theorem eq_card_67 : card_67 = combine (1, 1) [placed 1 (0, 1) card_8, placed 5 (0, 4) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_67 : Valid card_67 := by
  rw [eq_card_67]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_8
  subst c
  exact placed_valid 5 (0, 4) valid_32

theorem eq_card_68 : card_68 = combine (0, 2) [placed 7 (1, 6) card_0, placed 1 (0, 0) card_1] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_68 : Valid card_68 := by
  rw [eq_card_68]
  apply combination_rule (0, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 6) valid_0
  subst c
  exact placed_valid 1 (0, 0) valid_1

theorem eq_card_69 : card_69 = combine (3, 1) [placed 2 (0, 2) card_5, placed 4 (3, 0) card_15] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_69 : Valid card_69 := by
  rw [eq_card_69]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_15

theorem eq_card_70 : card_70 = combine (1, 3) [placed 7 (1, 4) card_2, placed 1 (0, 0) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_70 : Valid card_70 := by
  rw [eq_card_70]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_2
  subst c
  exact placed_valid 1 (0, 0) valid_3

theorem eq_card_71 : card_71 = combine (2, 1) [placed 4 (4, 1) card_0, placed 4 (2, 0) card_10] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_71 : Valid card_71 := by
  rw [eq_card_71]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 4 (2, 0) valid_10

theorem eq_card_72 : card_72 = combine (3, 2) [placed 1 (0, 1) card_20, placed 5 (0, 2) card_29, placed 0 (0, 0) card_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_72 : Valid card_72 := by
  rw [eq_card_72]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_29
  subst c
  exact placed_valid 0 (0, 0) valid_46

theorem eq_card_73 : card_73 = combine (2, 3) [placed 6 (4, 3) card_0, placed 0 (1, 0) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_73 : Valid card_73 := by
  rw [eq_card_73]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 0 (1, 0) valid_52

theorem eq_card_74 : card_74 = combine (1, 3) [placed 0 (0, 0) card_30, placed 4 (1, 0) card_30, placed 0 (0, 0) card_36, placed 4 (1, 0) card_36] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_74 : Valid card_74 := by
  rw [eq_card_74]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_36
  subst c
  exact placed_valid 4 (1, 0) valid_36

theorem eq_card_75 : card_75 = combine (0, 4) [placed 0 (0, 2) card_20, placed 6 (1, 5) card_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_75 : Valid card_75 := by
  rw [eq_card_75]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_20
  subst c
  exact placed_valid 6 (1, 5) valid_23

theorem eq_card_76 : card_76 = combine (1, 4) [placed 7 (1, 4) card_4, placed 5 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_76 : Valid card_76 := by
  rw [eq_card_76]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 5 (1, 4) valid_5

theorem eq_card_77 : card_77 = combine (2, 1) [placed 0 (0, 1) card_3, placed 5 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_77 : Valid card_77 := by
  rw [eq_card_77]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_3
  subst c
  exact placed_valid 5 (1, 4) valid_5

theorem eq_card_78 : card_78 = combine (3, 0) [placed 2 (0, 1) card_5, placed 3 (4, 0) card_77] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_78 : Valid card_78 := by
  rw [eq_card_78]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 3 (4, 0) valid_77

theorem eq_card_79 : card_79 = combine (3, 4) [placed 1 (2, 1) card_8, placed 7 (4, 4) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_79 : Valid card_79 := by
  rw [eq_card_79]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_8
  subst c
  exact placed_valid 7 (4, 4) valid_78

theorem eq_card_80 : card_80 = combine (1, 3) [placed 5 (1, 4) card_5, placed 7 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_80 : Valid card_80 := by
  rw [eq_card_80]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 7 (1, 4) valid_5

theorem eq_card_81 : card_81 = combine (3, 2) [placed 0 (0, 1) card_5, placed 0 (2, 0) card_42] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_81 : Valid card_81 := by
  rw [eq_card_81]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_42

theorem eq_card_82 : card_82 = combine (4, 3) [placed 0 (3, 0) card_52, placed 1 (0, 2) card_64] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_82 : Valid card_82 := by
  rw [eq_card_82]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_52
  subst c
  exact placed_valid 1 (0, 2) valid_64

theorem eq_card_83 : card_83 = combine (1, 4) [placed 5 (1, 4) card_5, placed 7 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_83 : Valid card_83 := by
  rw [eq_card_83]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 7 (1, 4) valid_5

theorem eq_card_84 : card_84 = combine (1, 5) [placed 6 (1, 5) card_6, placed 0 (0, 2) card_17] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_84 : Valid card_84 := by
  rw [eq_card_84]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 5) valid_6
  subst c
  exact placed_valid 0 (0, 2) valid_17

theorem eq_card_85 : card_85 = combine (2, 5) [placed 6 (2, 6) card_15, placed 2 (1, 7) card_65, placed 5 (0, 5) card_72] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_85 : Valid card_85 := by
  rw [eq_card_85]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_65
  subst c
  exact placed_valid 5 (0, 5) valid_72

theorem eq_card_86 : card_86 = combine (1, 2) [placed 7 (1, 5) card_2, placed 7 (4, 4) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_86 : Valid card_86 := by
  rw [eq_card_86]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_2
  subst c
  exact placed_valid 7 (4, 4) valid_78

theorem eq_card_87 : card_87 = combine (4, 2) [placed 0 (3, 0) card_11, placed 7 (4, 4) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_87 : Valid card_87 := by
  rw [eq_card_87]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_11
  subst c
  exact placed_valid 7 (4, 4) valid_35

theorem eq_card_88 : card_88 = combine (3, 4) [placed 1 (0, 3) card_52, placed 0 (2, 0) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_88 : Valid card_88 := by
  rw [eq_card_88]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_52
  subst c
  exact placed_valid 0 (2, 0) valid_53

theorem eq_card_89 : card_89 = combine (1, 4) [placed 7 (1, 4) card_4, placed 0 (1, 0) card_7] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_89 : Valid card_89 := by
  rw [eq_card_89]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 0 (1, 0) valid_7

theorem eq_card_90 : card_90 = combine (4, 1) [placed 5 (0, 1) card_6, placed 1 (1, 0) card_37] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_90 : Valid card_90 := by
  rw [eq_card_90]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_6
  subst c
  exact placed_valid 1 (1, 0) valid_37

theorem eq_card_91 : card_91 = combine (1, 4) [placed 7 (1, 4) card_4, placed 0 (1, 1) card_16] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_91 : Valid card_91 := by
  rw [eq_card_91]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 0 (1, 1) valid_16

theorem eq_card_92 : card_92 = combine (3, 3) [placed 0 (0, 2) card_5, placed 0 (0, 0) card_69] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_92 : Valid card_92 := by
  rw [eq_card_92]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_69

theorem eq_card_93 : card_93 = combine (4, 1) [placed 1 (0, 1) card_6, placed 5 (1, 1) card_21] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_93 : Valid card_93 := by
  rw [eq_card_93]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_6
  subst c
  exact placed_valid 5 (1, 1) valid_21

theorem eq_card_94 : card_94 = combine (0, 3) [placed 5 (0, 4) card_0, placed 1 (0, 0) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_94 : Valid card_94 := by
  rw [eq_card_94]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_0
  subst c
  exact placed_valid 1 (0, 0) valid_5

theorem eq_card_95 : card_95 = combine (1, 5) [placed 0 (0, 2) card_19, placed 2 (0, 7) card_19, placed 1 (0, 3) card_49, placed 5 (0, 6) card_49] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_95 : Valid card_95 := by
  rw [eq_card_95]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_49
  subst c
  exact placed_valid 5 (0, 6) valid_49

theorem eq_card_96 : card_96 = combine (3, 0) [placed 3 (3, 0) card_4, placed 2 (0, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_96 : Valid card_96 := by
  rw [eq_card_96]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 0) valid_4
  subst c
  exact placed_valid 2 (0, 1) valid_5

theorem eq_card_97 : card_97 = combine (1, 2) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_24] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_97 : Valid card_97 := by
  rw [eq_card_97]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_24

theorem eq_card_98 : card_98 = combine (0, 2) [placed 5 (0, 4) card_5, placed 0 (0, 1) card_16] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_98 : Valid card_98 := by
  rw [eq_card_98]
  apply combination_rule (0, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_16

theorem eq_card_99 : card_99 = combine (3, 2) [placed 2 (0, 3) card_5, placed 4 (3, 0) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_99 : Valid card_99 := by
  rw [eq_card_99]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_44

theorem eq_card_100 : card_100 = combine (4, 1) [placed 2 (0, 2) card_2, placed 4 (4, 0) card_10] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_100 : Valid card_100 := by
  rw [eq_card_100]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_2
  subst c
  exact placed_valid 4 (4, 0) valid_10

theorem eq_card_101 : card_101 = combine (0, 3) [placed 1 (0, 0) card_0, placed 0 (0, 1) card_51] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_101 : Valid card_101 := by
  rw [eq_card_101]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_51

theorem eq_card_102 : card_102 = combine (1, 3) [placed 7 (1, 5) card_0, placed 5 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_102 : Valid card_102 := by
  rw [eq_card_102]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 5 (1, 4) valid_5

theorem eq_card_103 : card_103 = combine (0, 4) [placed 0 (0, 0) card_6, placed 0 (0, 0) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_103 : Valid card_103 := by
  rw [eq_card_103]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_6
  subst c
  exact placed_valid 0 (0, 0) valid_11

theorem eq_card_104 : card_104 = combine (1, 4) [placed 0 (0, 2) card_10, placed 2 (0, 6) card_10, placed 4 (1, 2) card_52, placed 6 (1, 6) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_104 : Valid card_104 := by
  rw [eq_card_104]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 2) valid_52
  subst c
  exact placed_valid 6 (1, 6) valid_52

theorem eq_card_105 : card_105 = combine (0, 3) [placed 1 (0, 1) card_5, placed 0 (0, 0) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_105 : Valid card_105 := by
  rw [eq_card_105]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_11

theorem eq_card_106 : card_106 = combine (1, 1) [placed 7 (1, 4) card_4, placed 0 (1, 0) card_7] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_106 : Valid card_106 := by
  rw [eq_card_106]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 0 (1, 0) valid_7

theorem eq_card_107 : card_107 = combine (1, 2) [placed 7 (1, 4) card_3, placed 0 (0, 1) card_18] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_107 : Valid card_107 := by
  rw [eq_card_107]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_3
  subst c
  exact placed_valid 0 (0, 1) valid_18

theorem eq_card_108 : card_108 = combine (1, 1) [placed 0 (1, 0) card_15, placed 5 (0, 3) card_102] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_108 : Valid card_108 := by
  rw [eq_card_108]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_15
  subst c
  exact placed_valid 5 (0, 3) valid_102

theorem eq_card_109 : card_109 = combine (2, 3) [placed 2 (0, 3) card_5, placed 4 (3, 0) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_109 : Valid card_109 := by
  rw [eq_card_109]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_44

theorem eq_card_110 : card_110 = combine (3, 4) [placed 4 (4, 0) card_12, placed 3 (4, 2) card_28, placed 0 (0, 1) card_58, placed 0 (0, 1) card_100] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_110 : Valid card_110 := by
  rw [eq_card_110]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 2) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_58
  subst c
  exact placed_valid 0 (0, 1) valid_100

theorem eq_card_111 : card_111 = combine (4, 3) [placed 1 (1, 2) card_17, placed 4 (4, 0) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_111 : Valid card_111 := by
  rw [eq_card_111]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_17
  subst c
  exact placed_valid 4 (4, 0) valid_55

theorem eq_card_112 : card_112 = combine (2, 3) [placed 5 (0, 3) card_34, placed 0 (1, 0) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_112 : Valid card_112 := by
  rw [eq_card_112]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_34
  subst c
  exact placed_valid 0 (1, 0) valid_44

theorem eq_card_113 : card_113 = combine (1, 3) [placed 1 (0, 0) card_0, placed 0 (0, 2) card_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_113 : Valid card_113 := by
  rw [eq_card_113]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 2) valid_23

theorem eq_card_114 : card_114 = combine (3, 4) [placed 0 (0, 3) card_5, placed 0 (2, 0) card_14] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_114 : Valid card_114 := by
  rw [eq_card_114]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_14

theorem eq_card_115 : card_115 = combine (3, 2) [placed 2 (0, 3) card_5, placed 0 (0, 0) card_114] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_115 : Valid card_115 := by
  rw [eq_card_115]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_114

theorem eq_card_116 : card_116 = combine (4, 3) [placed 1 (0, 3) card_7, placed 1 (0, 2) card_9, placed 4 (4, 0) card_115] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_116 : Valid card_116 := by
  rw [eq_card_116]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_9
  subst c
  exact placed_valid 4 (4, 0) valid_115

theorem eq_card_117 : card_117 = combine (4, 3) [placed 5 (0, 3) card_7, placed 5 (0, 4) card_9, placed 4 (4, 0) card_115] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_117 : Valid card_117 := by
  rw [eq_card_117]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_9
  subst c
  exact placed_valid 4 (4, 0) valid_115

theorem eq_card_118 : card_118 = combine (4, 3) [placed 5 (0, 3) card_7, placed 1 (0, 2) card_9, placed 0 (1, 0) card_115] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_118 : Valid card_118 := by
  rw [eq_card_118]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_9
  subst c
  exact placed_valid 0 (1, 0) valid_115

theorem eq_card_119 : card_119 = combine (2, 3) [placed 2 (0, 3) card_5, placed 0 (0, 0) card_114] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_119 : Valid card_119 := by
  rw [eq_card_119]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_114

theorem eq_card_120 : card_120 = combine (2, 3) [placed 5 (0, 3) card_44, placed 5 (0, 3) card_52, placed 0 (0, 0) card_116] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_120 : Valid card_120 := by
  rw [eq_card_120]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_52
  subst c
  exact placed_valid 0 (0, 0) valid_116

theorem eq_card_121 : card_121 = combine (3, 0) [placed 5 (2, 4) card_1, placed 2 (0, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_121 : Valid card_121 := by
  rw [eq_card_121]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_1
  subst c
  exact placed_valid 2 (0, 1) valid_5

theorem eq_card_122 : card_122 = combine (2, 4) [placed 1 (1, 1) card_8, placed 5 (0, 4) card_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_122 : Valid card_122 := by
  rw [eq_card_122]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_8
  subst c
  exact placed_valid 5 (0, 4) valid_46

theorem eq_card_123 : card_123 = combine (4, 1) [placed 4 (4, 1) card_4, placed 6 (4, 1) card_4] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_123 : Valid card_123 := by
  rw [eq_card_123]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_4
  subst c
  exact placed_valid 6 (4, 1) valid_4

theorem eq_card_124 : card_124 = combine (2, 1) [placed 5 (1, 4) card_5, placed 1 (0, 1) card_123] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_124 : Valid card_124 := by
  rw [eq_card_124]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_123

theorem eq_card_125 : card_125 = combine (1, 2) [placed 7 (1, 4) card_5, placed 0 (0, 0) card_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_125 : Valid card_125 := by
  rw [eq_card_125]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_124

theorem eq_card_126 : card_126 = combine (1, 2) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_123] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_126 : Valid card_126 := by
  rw [eq_card_126]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_123

theorem eq_card_127 : card_127 = combine (1, 5) [placed 2 (1, 6) card_7, placed 1 (0, 2) card_24, placed 0 (0, 1) card_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_127 : Valid card_127 := by
  rw [eq_card_127]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_24
  subst c
  exact placed_valid 0 (0, 1) valid_124

theorem block01_valid : Valid card_64 ∧ Valid card_65 ∧ Valid card_66 ∧ Valid card_67 ∧ Valid card_68 ∧ Valid card_69 ∧ Valid card_70 ∧ Valid card_71 ∧ Valid card_72 ∧ Valid card_73 ∧ Valid card_74 ∧ Valid card_75 ∧ Valid card_76 ∧ Valid card_77 ∧ Valid card_78 ∧ Valid card_79 ∧ Valid card_80 ∧ Valid card_81 ∧ Valid card_82 ∧ Valid card_83 ∧ Valid card_84 ∧ Valid card_85 ∧ Valid card_86 ∧ Valid card_87 ∧ Valid card_88 ∧ Valid card_89 ∧ Valid card_90 ∧ Valid card_91 ∧ Valid card_92 ∧ Valid card_93 ∧ Valid card_94 ∧ Valid card_95 ∧ Valid card_96 ∧ Valid card_97 ∧ Valid card_98 ∧ Valid card_99 ∧ Valid card_100 ∧ Valid card_101 ∧ Valid card_102 ∧ Valid card_103 ∧ Valid card_104 ∧ Valid card_105 ∧ Valid card_106 ∧ Valid card_107 ∧ Valid card_108 ∧ Valid card_109 ∧ Valid card_110 ∧ Valid card_111 ∧ Valid card_112 ∧ Valid card_113 ∧ Valid card_114 ∧ Valid card_115 ∧ Valid card_116 ∧ Valid card_117 ∧ Valid card_118 ∧ Valid card_119 ∧ Valid card_120 ∧ Valid card_121 ∧ Valid card_122 ∧ Valid card_123 ∧ Valid card_124 ∧ Valid card_125 ∧ Valid card_126 ∧ Valid card_127 ∧ True :=
  ⟨valid_64, valid_65, valid_66, valid_67, valid_68, valid_69, valid_70, valid_71, valid_72, valid_73, valid_74, valid_75, valid_76, valid_77, valid_78, valid_79, valid_80, valid_81, valid_82, valid_83, valid_84, valid_85, valid_86, valid_87, valid_88, valid_89, valid_90, valid_91, valid_92, valid_93, valid_94, valid_95, valid_96, valid_97, valid_98, valid_99, valid_100, valid_101, valid_102, valid_103, valid_104, valid_105, valid_106, valid_107, valid_108, valid_109, valid_110, valid_111, valid_112, valid_113, valid_114, valid_115, valid_116, valid_117, valid_118, valid_119, valid_120, valid_121, valid_122, valid_123, valid_124, valid_125, valid_126, valid_127, True.intro⟩

end OAI.Snaky21.Certificate

theorem solution : Valid card_64 ∧ Valid card_65 ∧ Valid card_66 ∧ Valid card_67 ∧ Valid card_68 ∧ Valid card_69 ∧ Valid card_70 ∧ Valid card_71 ∧ Valid card_72 ∧ Valid card_73 ∧ Valid card_74 ∧ Valid card_75 ∧ Valid card_76 ∧ Valid card_77 ∧ Valid card_78 ∧ Valid card_79 ∧ Valid card_80 ∧ Valid card_81 ∧ Valid card_82 ∧ Valid card_83 ∧ Valid card_84 ∧ Valid card_85 ∧ Valid card_86 ∧ Valid card_87 ∧ Valid card_88 ∧ Valid card_89 ∧ Valid card_90 ∧ Valid card_91 ∧ Valid card_92 ∧ Valid card_93 ∧ Valid card_94 ∧ Valid card_95 ∧ Valid card_96 ∧ Valid card_97 ∧ Valid card_98 ∧ Valid card_99 ∧ Valid card_100 ∧ Valid card_101 ∧ Valid card_102 ∧ Valid card_103 ∧ Valid card_104 ∧ Valid card_105 ∧ Valid card_106 ∧ Valid card_107 ∧ Valid card_108 ∧ Valid card_109 ∧ Valid card_110 ∧ Valid card_111 ∧ Valid card_112 ∧ Valid card_113 ∧ Valid card_114 ∧ Valid card_115 ∧ Valid card_116 ∧ Valid card_117 ∧ Valid card_118 ∧ Valid card_119 ∧ Valid card_120 ∧ Valid card_121 ∧ Valid card_122 ∧ Valid card_123 ∧ Valid card_124 ∧ Valid card_125 ∧ Valid card_126 ∧ Valid card_127 ∧ True := block01_valid
