-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part09_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:09:39.758191+00:00
-- url     : https://prove2.me/submissions/5b0c23b7-2e47-4a27-ba51-c91dcdf8ebbc

import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part07_valid
import Definitions.Def_Snaky21Calc11Part04
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part08_valid
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
theorem valid_508 : Valid card_508 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_605 : Valid card_605 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_645 : Valid card_645 := block10_valid.2.2.2.2.2.1
theorem valid_647 : Valid card_647 := block10_valid.2.2.2.2.2.2.2.1
theorem valid_650 : Valid card_650 := block10_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_654 : Valid card_654 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_711 : Valid card_711 := block11_part07_valid.1

theorem calc11_card_1089_eq : placed 1 (2, 3) card_508 = calc11_card_1089 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1090_eq : placed 3 (8, 3) card_508 = calc11_card_1090 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1091_eq : placed 1 (2, 3) card_605 = calc11_card_1091 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1092_eq : placed 3 (8, 3) card_605 = calc11_card_1092 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1093_eq : placed 2 (1, 10) card_645 = calc11_card_1093 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1094_eq : placed 2 (1, 10) card_647 = calc11_card_1094 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1095_eq : placed 1 (0, 2) card_650 = calc11_card_1095 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1096_eq : placed 3 (10, 2) card_650 = calc11_card_1096 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1097_eq : placed 2 (2, 9) card_654 = calc11_card_1097 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1098_eq : placed 6 (8, 9) card_654 = calc11_card_1098 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1099_eq : placed 0 (1, 0) card_711 = calc11_card_1099 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1100_eq : calc11_card_1099.required ∪ ∅ = calc11_set_1100 := by decide +kernel

theorem calc11_set_1101_eq : calc11_card_1099.envelope ∪ ∅ = calc11_set_1101 := by decide +kernel

theorem calc11_set_1102_eq : calc11_card_1098.required ∪ calc11_set_1100 = calc11_set_1102 := by decide +kernel

theorem calc11_set_1103_eq : calc11_card_1098.envelope ∪ calc11_set_1101 = calc11_set_1103 := by decide +kernel

theorem calc11_set_1104_eq : calc11_card_1097.required ∪ calc11_set_1102 = calc11_set_1104 := by decide +kernel

theorem calc11_set_1105_eq : calc11_card_1097.envelope ∪ calc11_set_1103 = calc11_set_1105 := by decide +kernel

theorem calc11_set_1106_eq : calc11_card_1096.required ∪ calc11_set_1104 = calc11_set_1106 := by decide +kernel

theorem calc11_set_1107_eq : calc11_card_1096.envelope ∪ calc11_set_1105 = calc11_set_1107 := by decide +kernel

theorem calc11_set_1108_eq : calc11_card_1095.required ∪ calc11_set_1106 = calc11_set_1108 := by decide +kernel

theorem calc11_set_1109_eq : calc11_card_1095.envelope ∪ calc11_set_1107 = calc11_set_1109 := by decide +kernel

theorem calc11_set_1110_eq : calc11_card_1094.required ∪ calc11_set_1108 = calc11_set_1110 := by decide +kernel

theorem calc11_set_1111_eq : calc11_card_1094.envelope ∪ calc11_set_1109 = calc11_set_1111 := by decide +kernel

theorem calc11_set_1112_eq : calc11_card_1093.required ∪ calc11_set_1110 = calc11_set_1112 := by decide +kernel

theorem calc11_set_1113_eq : calc11_card_1093.envelope ∪ calc11_set_1111 = calc11_set_1113 := by decide +kernel

theorem calc11_set_1114_eq : calc11_card_1092.required ∪ calc11_set_1112 = calc11_set_1114 := by decide +kernel

theorem calc11_set_1115_eq : calc11_card_1092.envelope ∪ calc11_set_1113 = calc11_set_1115 := by decide +kernel

theorem calc11_set_1116_eq : calc11_card_1091.required ∪ calc11_set_1114 = calc11_set_1116 := by decide +kernel

theorem calc11_set_1117_eq : calc11_card_1091.envelope ∪ calc11_set_1115 = calc11_set_1117 := by decide +kernel

theorem calc11_set_1118_eq : calc11_card_1090.required ∪ calc11_set_1116 = calc11_set_1118 := by decide +kernel

theorem calc11_set_1119_eq : calc11_card_1090.envelope ∪ calc11_set_1117 = calc11_set_1119 := by decide +kernel

theorem calc11_set_1120_eq : calc11_card_1089.required ∪ calc11_set_1118 = calc11_set_1120 := by decide +kernel

theorem calc11_set_1121_eq : calc11_card_1089.envelope ∪ calc11_set_1119 = calc11_set_1121 := by decide +kernel

theorem calc11_set_1122_eq : calc11_card_1099.envelope ∩ calc11_card_1089.envelope = calc11_set_1122 := by decide +kernel

theorem calc11_set_1123_eq : calc11_card_1098.envelope ∩ calc11_set_1122 = calc11_set_1123 := by decide +kernel

theorem calc11_set_1124_eq : calc11_card_1097.envelope ∩ calc11_set_1123 = calc11_set_1124 := by decide +kernel

theorem calc11_set_1125_eq : calc11_card_1096.envelope ∩ calc11_set_1124 = calc11_set_1125 := by decide +kernel

theorem calc11_set_1126_eq : calc11_card_1095.envelope ∩ calc11_set_1125 = calc11_set_1126 := by decide +kernel

theorem calc11_set_1127_eq : calc11_card_1094.envelope ∩ calc11_set_1126 = calc11_set_1127 := by decide +kernel

theorem calc11_set_1128_eq : calc11_card_1093.envelope ∩ calc11_set_1127 = calc11_set_1128 := by decide +kernel

theorem calc11_set_1129_eq : calc11_card_1092.envelope ∩ calc11_set_1128 = calc11_set_1129 := by decide +kernel

theorem calc11_set_1130_eq : calc11_card_1091.envelope ∩ calc11_set_1129 = calc11_set_1130 := by decide +kernel

theorem calc11_set_1131_eq : calc11_card_1090.envelope ∩ calc11_set_1130 = calc11_set_1131 := by decide +kernel

theorem calc11_set_1132_eq : calc11_set_1120 ∪ calc11_set_1131 = calc11_set_1132 := by decide +kernel

theorem calc11_finishA_1133 : calc11_set_1132.erase (5, 6) = card_713.required := by decide +kernel

theorem calc11_finishT_1133 : insert (5, 6) calc11_set_1121 = card_713.envelope := by decide +kernel

theorem eq_card_713 : card_713 = combine (5, 6) [placed 1 (2, 3) card_508, placed 3 (8, 3) card_508, placed 1 (2, 3) card_605, placed 3 (8, 3) card_605, placed 2 (1, 10) card_645, placed 2 (1, 10) card_647, placed 1 (0, 2) card_650, placed 3 (10, 2) card_650, placed 2 (2, 9) card_654, placed 6 (8, 9) card_654, placed 0 (1, 0) card_711] := by
  rw [calc11_card_1089_eq, calc11_card_1090_eq, calc11_card_1091_eq, calc11_card_1092_eq, calc11_card_1093_eq, calc11_card_1094_eq, calc11_card_1095_eq, calc11_card_1096_eq, calc11_card_1097_eq, calc11_card_1098_eq, calc11_card_1099_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1100_eq, calc11_set_1102_eq, calc11_set_1104_eq, calc11_set_1106_eq, calc11_set_1108_eq, calc11_set_1110_eq, calc11_set_1112_eq, calc11_set_1114_eq, calc11_set_1116_eq, calc11_set_1118_eq, calc11_set_1120_eq, calc11_set_1122_eq, calc11_set_1123_eq, calc11_set_1124_eq, calc11_set_1125_eq, calc11_set_1126_eq, calc11_set_1127_eq, calc11_set_1128_eq, calc11_set_1129_eq, calc11_set_1130_eq, calc11_set_1131_eq, calc11_set_1132_eq, calc11_finishA_1133]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1101_eq, calc11_set_1103_eq, calc11_set_1105_eq, calc11_set_1107_eq, calc11_set_1109_eq, calc11_set_1111_eq, calc11_set_1113_eq, calc11_set_1115_eq, calc11_set_1117_eq, calc11_set_1119_eq, calc11_set_1121_eq, calc11_finishT_1133]
  · decide +kernel

theorem valid_713 : Valid card_713 := by
  rw [eq_card_713]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_645
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_647
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_654
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_654
  subst c
  exact placed_valid 0 (1, 0) valid_711


end OAI.Snaky21.Certificate

theorem solution : Valid card_713 ∧ True :=
  ⟨valid_713, True.intro⟩
