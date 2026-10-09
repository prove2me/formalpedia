-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part10_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:10:56.488742+00:00
-- url     : https://prove2.me/submissions/0fe6c3ce-e7d4-489d-8866-00b446a82b61

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Definitions.Def_Snaky21Calc11Part05
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part09_valid
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
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_41 : Valid card_41 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_55 : Valid card_55 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_88 : Valid card_88 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calc11_card_1134_eq : placed 0 (2, 3) card_41 = calc11_card_1134 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1135_eq : placed 5 (0, 6) card_55 = calc11_card_1135 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1136_eq : calc11_card_1135.required ∪ ∅ = calc11_set_1136 := by decide +kernel

theorem calc11_set_1137_eq : calc11_card_1135.envelope ∪ ∅ = calc11_set_1137 := by decide +kernel

theorem calc11_set_1138_eq : calc11_card_1134.required ∪ calc11_set_1136 = calc11_set_1138 := by decide +kernel

theorem calc11_set_1139_eq : calc11_card_1134.envelope ∪ calc11_set_1137 = calc11_set_1139 := by decide +kernel

theorem calc11_set_1140_eq : calc11_card_1135.envelope ∩ calc11_card_1134.envelope = calc11_set_1140 := by decide +kernel

theorem calc11_set_1141_eq : calc11_set_1138 ∪ calc11_set_1140 = calc11_set_1141 := by decide +kernel

theorem calc11_finishA_1142 : calc11_set_1141.erase (3, 6) = inline_842.required := by decide +kernel

theorem calc11_finishT_1142 : insert (3, 6) calc11_set_1139 = inline_842.envelope := by decide +kernel

theorem eq_inline_842 : inline_842 = combine (3, 6) [placed 0 (2, 3) card_41, placed 5 (0, 6) card_55] := by
  rw [calc11_card_1134_eq, calc11_card_1135_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1136_eq, calc11_set_1138_eq, calc11_set_1140_eq, calc11_set_1141_eq, calc11_finishA_1142]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1137_eq, calc11_set_1139_eq, calc11_finishT_1142]
  · decide +kernel

theorem valid_inline_842 : Valid inline_842 := by
  rw [eq_inline_842]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_41
  subst c
  exact placed_valid 5 (0, 6) valid_55

theorem calc11_card_1143_eq : placed 4 (3, 2) card_15 = calc11_card_1143 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1144_eq : placed 5 (0, 6) card_88 = calc11_card_1144 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1145_eq : inline_842.required ∪ ∅ = calc11_set_1145 := by decide +kernel

theorem calc11_set_1146_eq : inline_842.envelope ∪ ∅ = calc11_set_1146 := by decide +kernel

theorem calc11_set_1147_eq : calc11_card_1144.required ∪ calc11_set_1145 = calc11_set_1147 := by decide +kernel

theorem calc11_set_1148_eq : calc11_card_1144.envelope ∪ calc11_set_1146 = calc11_set_1148 := by decide +kernel

theorem calc11_set_1149_eq : calc11_card_1143.required ∪ calc11_set_1147 = calc11_set_1149 := by decide +kernel

theorem calc11_set_1150_eq : calc11_card_1143.envelope ∪ calc11_set_1148 = calc11_set_1150 := by decide +kernel

theorem calc11_set_1151_eq : inline_842.envelope ∩ calc11_card_1143.envelope = calc11_set_1151 := by decide +kernel

theorem calc11_set_1152_eq : calc11_card_1144.envelope ∩ calc11_set_1151 = calc11_set_1152 := by decide +kernel

theorem calc11_set_1153_eq : calc11_set_1149 ∪ calc11_set_1152 = calc11_set_1153 := by decide +kernel

theorem calc11_finishA_1154 : calc11_set_1153.erase (3, 3) = card_714.required := by decide +kernel

theorem calc11_finishT_1154 : insert (3, 3) calc11_set_1150 = card_714.envelope := by decide +kernel

theorem eq_card_714 : card_714 = combine (3, 3) [placed 4 (3, 2) card_15, placed 5 (0, 6) card_88, inline_842] := by
  rw [calc11_card_1143_eq, calc11_card_1144_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1145_eq, calc11_set_1147_eq, calc11_set_1149_eq, calc11_set_1151_eq, calc11_set_1152_eq, calc11_set_1153_eq, calc11_finishA_1154]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1146_eq, calc11_set_1148_eq, calc11_set_1150_eq, calc11_finishT_1154]
  · decide +kernel

theorem valid_714 : Valid card_714 := by
  rw [eq_card_714]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_88
  subst c
  exact valid_inline_842


end OAI.Snaky21.Certificate

theorem solution : Valid card_714 ∧ True :=
  ⟨valid_714, True.intro⟩
