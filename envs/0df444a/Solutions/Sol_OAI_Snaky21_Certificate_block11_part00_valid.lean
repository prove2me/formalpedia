-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part00_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:53:52.436977+00:00
-- url     : https://prove2.me/submissions/bd03648e-0eb5-48b1-ac83-5911413d2f1c

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Definitions.Def_Snaky21Calc11Part00
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
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
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_25 : Valid card_25 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_28 : Valid card_28 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_30 : Valid card_30 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_58 : Valid card_58 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_78 : Valid card_78 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_306 : Valid card_306 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_400 : Valid card_400 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_516 : Valid card_516 := block08_valid.2.2.2.2.1
theorem valid_703 : Valid card_703 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calc11_card_0_eq : placed 3 (5, 4) card_28 = calc11_card_0 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1_eq : placed 0 (1, 3) card_58 = calc11_card_1 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2_eq : placed 0 (1, 2) card_306 = calc11_card_2 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_3_eq : calc11_card_2.required ∪ ∅ = calc11_set_3 := by decide +kernel

theorem calc11_set_4_eq : calc11_card_2.envelope ∪ ∅ = calc11_set_4 := by decide +kernel

theorem calc11_set_5_eq : calc11_card_1.required ∪ calc11_set_3 = calc11_set_5 := by decide +kernel

theorem calc11_set_6_eq : calc11_card_1.envelope ∪ calc11_set_4 = calc11_set_6 := by decide +kernel

theorem calc11_set_7_eq : calc11_card_0.required ∪ calc11_set_5 = calc11_set_7 := by decide +kernel

theorem calc11_set_8_eq : calc11_card_0.envelope ∪ calc11_set_6 = calc11_set_8 := by decide +kernel

theorem calc11_set_9_eq : calc11_card_2.envelope ∩ calc11_card_0.envelope = calc11_set_9 := by decide +kernel

theorem calc11_set_10_eq : calc11_card_1.envelope ∩ calc11_set_9 = calc11_set_10 := by decide +kernel

theorem calc11_set_11_eq : calc11_set_7 ∪ calc11_set_10 = calc11_set_11 := by decide +kernel

theorem calc11_finishA_12 : calc11_set_11.erase (4, 6) = inline_794.required := by decide +kernel

theorem calc11_finishT_12 : insert (4, 6) calc11_set_8 = inline_794.envelope := by decide +kernel

theorem eq_inline_794 : inline_794 = combine (4, 6) [placed 3 (5, 4) card_28, placed 0 (1, 3) card_58, placed 0 (1, 2) card_306] := by
  rw [calc11_card_0_eq, calc11_card_1_eq, calc11_card_2_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_3_eq, calc11_set_5_eq, calc11_set_7_eq, calc11_set_9_eq, calc11_set_10_eq, calc11_set_11_eq, calc11_finishA_12]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_4_eq, calc11_set_6_eq, calc11_set_8_eq, calc11_finishT_12]
  · decide +kernel

theorem valid_inline_794 : Valid inline_794 := by
  rw [eq_inline_794]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 4) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_58
  subst c
  exact placed_valid 0 (1, 2) valid_306

theorem calc11_card_13_eq : placed 6 (5, 5) card_2 = calc11_card_13 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_14_eq : placed 0 (4, 2) card_52 = calc11_card_14 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_15_eq : calc11_card_14.required ∪ ∅ = calc11_set_15 := by decide +kernel

theorem calc11_set_16_eq : calc11_card_14.envelope ∪ ∅ = calc11_set_16 := by decide +kernel

theorem calc11_set_17_eq : calc11_card_13.required ∪ calc11_set_15 = calc11_set_17 := by decide +kernel

theorem calc11_set_18_eq : calc11_card_13.envelope ∪ calc11_set_16 = calc11_set_18 := by decide +kernel

theorem calc11_set_19_eq : calc11_card_14.envelope ∩ calc11_card_13.envelope = calc11_set_19 := by decide +kernel

theorem calc11_set_20_eq : calc11_set_17 ∪ calc11_set_19 = calc11_set_20 := by decide +kernel

theorem calc11_finishA_21 : calc11_set_20.erase (5, 5) = inline_795.required := by decide +kernel

theorem calc11_finishT_21 : insert (5, 5) calc11_set_18 = inline_795.envelope := by decide +kernel

theorem eq_inline_795 : inline_795 = combine (5, 5) [placed 6 (5, 5) card_2, placed 0 (4, 2) card_52] := by
  rw [calc11_card_13_eq, calc11_card_14_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_15_eq, calc11_set_17_eq, calc11_set_19_eq, calc11_set_20_eq, calc11_finishA_21]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_16_eq, calc11_set_18_eq, calc11_finishT_21]
  · decide +kernel

theorem valid_inline_795 : Valid inline_795 := by
  rw [eq_inline_795]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 5) valid_2
  subst c
  exact placed_valid 0 (4, 2) valid_52

theorem calc11_card_22_eq : placed 6 (5, 5) card_2 = calc11_card_22 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_23_eq : placed 6 (5, 6) card_10 = calc11_card_23 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_24_eq : calc11_card_23.required ∪ ∅ = calc11_set_24 := by decide +kernel

theorem calc11_set_25_eq : calc11_card_23.envelope ∪ ∅ = calc11_set_25 := by decide +kernel

theorem calc11_set_26_eq : calc11_card_22.required ∪ calc11_set_24 = calc11_set_26 := by decide +kernel

theorem calc11_set_27_eq : calc11_card_22.envelope ∪ calc11_set_25 = calc11_set_27 := by decide +kernel

theorem calc11_set_28_eq : calc11_card_23.envelope ∩ calc11_card_22.envelope = calc11_set_28 := by decide +kernel

theorem calc11_set_29_eq : calc11_set_26 ∪ calc11_set_28 = calc11_set_29 := by decide +kernel

theorem calc11_finishA_30 : calc11_set_29.erase (5, 5) = inline_796.required := by decide +kernel

theorem calc11_finishT_30 : insert (5, 5) calc11_set_27 = inline_796.envelope := by decide +kernel

theorem eq_inline_796 : inline_796 = combine (5, 5) [placed 6 (5, 5) card_2, placed 6 (5, 6) card_10] := by
  rw [calc11_card_22_eq, calc11_card_23_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_24_eq, calc11_set_26_eq, calc11_set_28_eq, calc11_set_29_eq, calc11_finishA_30]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_25_eq, calc11_set_27_eq, calc11_finishT_30]
  · decide +kernel

theorem valid_inline_796 : Valid inline_796 := by
  rw [eq_inline_796]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 5) valid_2
  subst c
  exact placed_valid 6 (5, 6) valid_10

theorem calc11_card_31_eq : placed 3 (5, 3) card_25 = calc11_card_31 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_32_eq : placed 7 (5, 6) card_78 = calc11_card_32 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_33_eq : calc11_card_32.required ∪ ∅ = calc11_set_33 := by decide +kernel

theorem calc11_set_34_eq : calc11_card_32.envelope ∪ ∅ = calc11_set_34 := by decide +kernel

theorem calc11_set_35_eq : calc11_card_31.required ∪ calc11_set_33 = calc11_set_35 := by decide +kernel

theorem calc11_set_36_eq : calc11_card_31.envelope ∪ calc11_set_34 = calc11_set_36 := by decide +kernel

theorem calc11_set_37_eq : calc11_card_32.envelope ∩ calc11_card_31.envelope = calc11_set_37 := by decide +kernel

theorem calc11_set_38_eq : calc11_set_35 ∪ calc11_set_37 = calc11_set_38 := by decide +kernel

theorem calc11_finishA_39 : calc11_set_38.erase (4, 6) = inline_797.required := by decide +kernel

theorem calc11_finishT_39 : insert (4, 6) calc11_set_36 = inline_797.envelope := by decide +kernel

theorem eq_inline_797 : inline_797 = combine (4, 6) [placed 3 (5, 3) card_25, placed 7 (5, 6) card_78] := by
  rw [calc11_card_31_eq, calc11_card_32_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_33_eq, calc11_set_35_eq, calc11_set_37_eq, calc11_set_38_eq, calc11_finishA_39]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_34_eq, calc11_set_36_eq, calc11_finishT_39]
  · decide +kernel

theorem valid_inline_797 : Valid inline_797 := by
  rw [eq_inline_797]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_25
  subst c
  exact placed_valid 7 (5, 6) valid_78

theorem calc11_card_40_eq : placed 2 (1, 6) card_516 = calc11_card_40 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_41_eq : inline_797.required ∪ ∅ = calc11_set_41 := by decide +kernel

theorem calc11_set_42_eq : inline_797.envelope ∪ ∅ = calc11_set_42 := by decide +kernel

theorem calc11_set_43_eq : inline_796.required ∪ calc11_set_41 = calc11_set_43 := by decide +kernel

theorem calc11_set_44_eq : inline_796.envelope ∪ calc11_set_42 = calc11_set_44 := by decide +kernel

theorem calc11_set_45_eq : inline_795.required ∪ calc11_set_43 = calc11_set_45 := by decide +kernel

theorem calc11_set_46_eq : inline_795.envelope ∪ calc11_set_44 = calc11_set_46 := by decide +kernel

theorem calc11_set_47_eq : calc11_card_40.required ∪ calc11_set_45 = calc11_set_47 := by decide +kernel

theorem calc11_set_48_eq : calc11_card_40.envelope ∪ calc11_set_46 = calc11_set_48 := by decide +kernel

theorem calc11_set_49_eq : inline_797.envelope ∩ calc11_card_40.envelope = calc11_set_49 := by decide +kernel

theorem calc11_set_50_eq : inline_796.envelope ∩ calc11_set_49 = calc11_set_50 := by decide +kernel

theorem calc11_set_51_eq : inline_795.envelope ∩ calc11_set_50 = calc11_set_51 := by decide +kernel

theorem calc11_set_52_eq : calc11_set_47 ∪ calc11_set_51 = calc11_set_52 := by decide +kernel

theorem calc11_finishA_53 : calc11_set_52.erase (4, 3) = inline_798.required := by decide +kernel

theorem calc11_finishT_53 : insert (4, 3) calc11_set_48 = inline_798.envelope := by decide +kernel

theorem eq_inline_798 : inline_798 = combine (4, 3) [placed 2 (1, 6) card_516, inline_795, inline_796, inline_797] := by
  rw [calc11_card_40_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_41_eq, calc11_set_43_eq, calc11_set_45_eq, calc11_set_47_eq, calc11_set_49_eq, calc11_set_50_eq, calc11_set_51_eq, calc11_set_52_eq, calc11_finishA_53]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_42_eq, calc11_set_44_eq, calc11_set_46_eq, calc11_set_48_eq, calc11_finishT_53]
  · decide +kernel

theorem valid_inline_798 : Valid inline_798 := by
  rw [eq_inline_798]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_516
  rcases hc with rfl | hc
  · exact valid_inline_795
  rcases hc with rfl | hc
  · exact valid_inline_796
  subst c
  exact valid_inline_797

theorem calc11_card_54_eq : placed 5 (1, 5) card_30 = calc11_card_54 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_55_eq : placed 0 (0, 0) card_703 = calc11_card_55 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_56_eq : inline_798.required ∪ ∅ = calc11_set_56 := by decide +kernel

theorem calc11_set_57_eq : inline_798.envelope ∪ ∅ = calc11_set_57 := by decide +kernel

theorem calc11_set_58_eq : calc11_card_55.required ∪ calc11_set_56 = calc11_set_58 := by decide +kernel

theorem calc11_set_59_eq : calc11_card_55.envelope ∪ calc11_set_57 = calc11_set_59 := by decide +kernel

theorem calc11_set_60_eq : inline_794.required ∪ calc11_set_58 = calc11_set_60 := by decide +kernel

theorem calc11_set_61_eq : inline_794.envelope ∪ calc11_set_59 = calc11_set_61 := by decide +kernel

theorem calc11_set_62_eq : calc11_card_54.required ∪ calc11_set_60 = calc11_set_62 := by decide +kernel

theorem calc11_set_63_eq : calc11_card_54.envelope ∪ calc11_set_61 = calc11_set_63 := by decide +kernel

theorem calc11_set_64_eq : inline_798.envelope ∩ calc11_card_54.envelope = calc11_set_64 := by decide +kernel

theorem calc11_set_65_eq : calc11_card_55.envelope ∩ calc11_set_64 = calc11_set_65 := by decide +kernel

theorem calc11_set_66_eq : inline_794.envelope ∩ calc11_set_65 = calc11_set_66 := by decide +kernel

theorem calc11_set_67_eq : calc11_set_62 ∪ calc11_set_66 = calc11_set_67 := by decide +kernel

theorem calc11_finishA_68 : calc11_set_67.erase (4, 5) = inline_799.required := by decide +kernel

theorem calc11_finishT_68 : insert (4, 5) calc11_set_63 = inline_799.envelope := by decide +kernel

theorem eq_inline_799 : inline_799 = combine (4, 5) [placed 5 (1, 5) card_30, inline_794, placed 0 (0, 0) card_703, inline_798] := by
  rw [calc11_card_54_eq, calc11_card_55_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_56_eq, calc11_set_58_eq, calc11_set_60_eq, calc11_set_62_eq, calc11_set_64_eq, calc11_set_65_eq, calc11_set_66_eq, calc11_set_67_eq, calc11_finishA_68]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_57_eq, calc11_set_59_eq, calc11_set_61_eq, calc11_set_63_eq, calc11_finishT_68]
  · decide +kernel

theorem valid_inline_799 : Valid inline_799 := by
  rw [eq_inline_799]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_30
  rcases hc with rfl | hc
  · exact valid_inline_794
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_703
  subst c
  exact valid_inline_798

theorem calc11_card_69_eq : placed 1 (0, 4) card_22 = calc11_card_69 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_70_eq : placed 2 (0, 6) card_400 = calc11_card_70 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_71_eq : inline_799.required ∪ ∅ = calc11_set_71 := by decide +kernel

theorem calc11_set_72_eq : inline_799.envelope ∪ ∅ = calc11_set_72 := by decide +kernel

theorem calc11_set_73_eq : calc11_card_70.required ∪ calc11_set_71 = calc11_set_73 := by decide +kernel

theorem calc11_set_74_eq : calc11_card_70.envelope ∪ calc11_set_72 = calc11_set_74 := by decide +kernel

theorem calc11_set_75_eq : calc11_card_69.required ∪ calc11_set_73 = calc11_set_75 := by decide +kernel

theorem calc11_set_76_eq : calc11_card_69.envelope ∪ calc11_set_74 = calc11_set_76 := by decide +kernel

theorem calc11_set_77_eq : inline_799.envelope ∩ calc11_card_69.envelope = calc11_set_77 := by decide +kernel

theorem calc11_set_78_eq : calc11_card_70.envelope ∩ calc11_set_77 = calc11_set_78 := by decide +kernel

theorem calc11_set_79_eq : calc11_set_75 ∪ calc11_set_78 = calc11_set_79 := by decide +kernel

theorem calc11_finishA_80 : calc11_set_79.erase (4, 4) = card_704.required := by decide +kernel

theorem calc11_finishT_80 : insert (4, 4) calc11_set_76 = card_704.envelope := by decide +kernel

theorem eq_card_704 : card_704 = combine (4, 4) [placed 1 (0, 4) card_22, placed 2 (0, 6) card_400, inline_799] := by
  rw [calc11_card_69_eq, calc11_card_70_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_71_eq, calc11_set_73_eq, calc11_set_75_eq, calc11_set_77_eq, calc11_set_78_eq, calc11_set_79_eq, calc11_finishA_80]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_72_eq, calc11_set_74_eq, calc11_set_76_eq, calc11_finishT_80]
  · decide +kernel

theorem valid_704 : Valid card_704 := by
  rw [eq_card_704]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_400
  subst c
  exact valid_inline_799


end OAI.Snaky21.Certificate

theorem solution : Valid card_704 ∧ True :=
  ⟨valid_704, True.intro⟩
