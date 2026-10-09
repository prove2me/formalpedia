-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part11_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:14:42.068514+00:00
-- url     : https://prove2.me/submissions/79dcfca8-f283-4e20-a5c8-f56f755ddb88

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Definitions.Def_Snaky21Calc11Part05
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part10_valid
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
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_30 : Valid card_30 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_74 : Valid card_74 := block01_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_110 : Valid card_110 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_111 : Valid card_111 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_134 : Valid card_134 := block02_valid.2.2.2.2.2.2.1
theorem valid_296 : Valid card_296 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_325 : Valid card_325 := block05_valid.2.2.2.2.2.1
theorem valid_361 : Valid card_361 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_394 : Valid card_394 := block06_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_408 : Valid card_408 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_511 : Valid card_511 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_523 : Valid card_523 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_532 : Valid card_532 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_536 : Valid card_536 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_545 : Valid card_545 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_621 : Valid card_621 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_655 : Valid card_655 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_664 : Valid card_664 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_714 : Valid card_714 := block11_part10_valid.1

theorem calc11_card_1155_eq : placed 6 (5, 8) card_53 = calc11_card_1155 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1156_eq : placed 0 (4, 2) card_53 = calc11_card_1156 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1157_eq : placed 0 (2, 2) card_111 = calc11_card_1157 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1158_eq : placed 1 (2, 4) card_394 = calc11_card_1158 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1159_eq : calc11_card_1158.required ∪ ∅ = calc11_set_1159 := by decide +kernel

theorem calc11_set_1160_eq : calc11_card_1158.envelope ∪ ∅ = calc11_set_1160 := by decide +kernel

theorem calc11_set_1161_eq : calc11_card_1157.required ∪ calc11_set_1159 = calc11_set_1161 := by decide +kernel

theorem calc11_set_1162_eq : calc11_card_1157.envelope ∪ calc11_set_1160 = calc11_set_1162 := by decide +kernel

theorem calc11_set_1163_eq : calc11_card_1156.required ∪ calc11_set_1161 = calc11_set_1163 := by decide +kernel

theorem calc11_set_1164_eq : calc11_card_1156.envelope ∪ calc11_set_1162 = calc11_set_1164 := by decide +kernel

theorem calc11_set_1165_eq : calc11_card_1155.required ∪ calc11_set_1163 = calc11_set_1165 := by decide +kernel

theorem calc11_set_1166_eq : calc11_card_1155.envelope ∪ calc11_set_1164 = calc11_set_1166 := by decide +kernel

theorem calc11_set_1167_eq : calc11_card_1158.envelope ∩ calc11_card_1155.envelope = calc11_set_1167 := by decide +kernel

theorem calc11_set_1168_eq : calc11_card_1157.envelope ∩ calc11_set_1167 = calc11_set_1168 := by decide +kernel

theorem calc11_set_1169_eq : calc11_card_1156.envelope ∩ calc11_set_1168 = calc11_set_1169 := by decide +kernel

theorem calc11_set_1170_eq : calc11_set_1165 ∪ calc11_set_1169 = calc11_set_1170 := by decide +kernel

theorem calc11_finishA_1171 : calc11_set_1170.erase (4, 4) = inline_843.required := by decide +kernel

theorem calc11_finishT_1171 : insert (4, 4) calc11_set_1166 = inline_843.envelope := by decide +kernel

theorem eq_inline_843 : inline_843 = combine (4, 4) [placed 6 (5, 8) card_53, placed 0 (4, 2) card_53, placed 0 (2, 2) card_111, placed 1 (2, 4) card_394] := by
  rw [calc11_card_1155_eq, calc11_card_1156_eq, calc11_card_1157_eq, calc11_card_1158_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1159_eq, calc11_set_1161_eq, calc11_set_1163_eq, calc11_set_1165_eq, calc11_set_1167_eq, calc11_set_1168_eq, calc11_set_1169_eq, calc11_set_1170_eq, calc11_finishA_1171]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1160_eq, calc11_set_1162_eq, calc11_set_1164_eq, calc11_set_1166_eq, calc11_finishT_1171]
  · decide +kernel

theorem valid_inline_843 : Valid inline_843 := by
  rw [eq_inline_843]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_111
  subst c
  exact placed_valid 1 (2, 4) valid_394

theorem calc11_card_1172_eq : placed 1 (2, 5) card_44 = calc11_card_1172 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1173_eq : placed 1 (2, 5) card_52 = calc11_card_1173 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1174_eq : placed 4 (6, 3) card_134 = calc11_card_1174 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1175_eq : inline_843.required ∪ ∅ = calc11_set_1175 := by decide +kernel

theorem calc11_set_1176_eq : inline_843.envelope ∪ ∅ = calc11_set_1176 := by decide +kernel

theorem calc11_set_1177_eq : calc11_card_1174.required ∪ calc11_set_1175 = calc11_set_1177 := by decide +kernel

theorem calc11_set_1178_eq : calc11_card_1174.envelope ∪ calc11_set_1176 = calc11_set_1178 := by decide +kernel

theorem calc11_set_1179_eq : calc11_card_1173.required ∪ calc11_set_1177 = calc11_set_1179 := by decide +kernel

theorem calc11_set_1180_eq : calc11_card_1173.envelope ∪ calc11_set_1178 = calc11_set_1180 := by decide +kernel

theorem calc11_set_1181_eq : calc11_card_1172.required ∪ calc11_set_1179 = calc11_set_1181 := by decide +kernel

theorem calc11_set_1182_eq : calc11_card_1172.envelope ∪ calc11_set_1180 = calc11_set_1182 := by decide +kernel

theorem calc11_set_1183_eq : inline_843.envelope ∩ calc11_card_1172.envelope = calc11_set_1183 := by decide +kernel

theorem calc11_set_1184_eq : calc11_card_1174.envelope ∩ calc11_set_1183 = calc11_set_1184 := by decide +kernel

theorem calc11_set_1185_eq : calc11_card_1173.envelope ∩ calc11_set_1184 = calc11_set_1185 := by decide +kernel

theorem calc11_set_1186_eq : calc11_set_1181 ∪ calc11_set_1185 = calc11_set_1186 := by decide +kernel

theorem calc11_finishA_1187 : calc11_set_1186.erase (3, 5) = inline_844.required := by decide +kernel

theorem calc11_finishT_1187 : insert (3, 5) calc11_set_1182 = inline_844.envelope := by decide +kernel

theorem eq_inline_844 : inline_844 = combine (3, 5) [placed 1 (2, 5) card_44, placed 1 (2, 5) card_52, placed 4 (6, 3) card_134, inline_843] := by
  rw [calc11_card_1172_eq, calc11_card_1173_eq, calc11_card_1174_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1175_eq, calc11_set_1177_eq, calc11_set_1179_eq, calc11_set_1181_eq, calc11_set_1183_eq, calc11_set_1184_eq, calc11_set_1185_eq, calc11_set_1186_eq, calc11_finishA_1187]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1176_eq, calc11_set_1178_eq, calc11_set_1180_eq, calc11_set_1182_eq, calc11_finishT_1187]
  · decide +kernel

theorem valid_inline_844 : Valid inline_844 := by
  rw [eq_inline_844]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_134
  subst c
  exact valid_inline_843

theorem calc11_card_1188_eq : placed 5 (4, 6) card_30 = calc11_card_1188 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1189_eq : placed 0 (4, 3) card_110 = calc11_card_1189 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1190_eq : placed 1 (3, 4) card_296 = calc11_card_1190 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1191_eq : placed 0 (4, 3) card_511 = calc11_card_1191 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1192_eq : calc11_card_1191.required ∪ ∅ = calc11_set_1192 := by decide +kernel

theorem calc11_set_1193_eq : calc11_card_1191.envelope ∪ ∅ = calc11_set_1193 := by decide +kernel

theorem calc11_set_1194_eq : calc11_card_1190.required ∪ calc11_set_1192 = calc11_set_1194 := by decide +kernel

theorem calc11_set_1195_eq : calc11_card_1190.envelope ∪ calc11_set_1193 = calc11_set_1195 := by decide +kernel

theorem calc11_set_1196_eq : calc11_card_1189.required ∪ calc11_set_1194 = calc11_set_1196 := by decide +kernel

theorem calc11_set_1197_eq : calc11_card_1189.envelope ∪ calc11_set_1195 = calc11_set_1197 := by decide +kernel

theorem calc11_set_1198_eq : calc11_card_1188.required ∪ calc11_set_1196 = calc11_set_1198 := by decide +kernel

theorem calc11_set_1199_eq : calc11_card_1188.envelope ∪ calc11_set_1197 = calc11_set_1199 := by decide +kernel

theorem calc11_set_1200_eq : calc11_card_1191.envelope ∩ calc11_card_1188.envelope = calc11_set_1200 := by decide +kernel

theorem calc11_set_1201_eq : calc11_card_1190.envelope ∩ calc11_set_1200 = calc11_set_1201 := by decide +kernel

theorem calc11_set_1202_eq : calc11_card_1189.envelope ∩ calc11_set_1201 = calc11_set_1202 := by decide +kernel

theorem calc11_set_1203_eq : calc11_set_1198 ∪ calc11_set_1202 = calc11_set_1203 := by decide +kernel

theorem calc11_finishA_1204 : calc11_set_1203.erase (7, 6) = inline_845.required := by decide +kernel

theorem calc11_finishT_1204 : insert (7, 6) calc11_set_1199 = inline_845.envelope := by decide +kernel

theorem eq_inline_845 : inline_845 = combine (7, 6) [placed 5 (4, 6) card_30, placed 0 (4, 3) card_110, placed 1 (3, 4) card_296, placed 0 (4, 3) card_511] := by
  rw [calc11_card_1188_eq, calc11_card_1189_eq, calc11_card_1190_eq, calc11_card_1191_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1192_eq, calc11_set_1194_eq, calc11_set_1196_eq, calc11_set_1198_eq, calc11_set_1200_eq, calc11_set_1201_eq, calc11_set_1202_eq, calc11_set_1203_eq, calc11_finishA_1204]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1193_eq, calc11_set_1195_eq, calc11_set_1197_eq, calc11_set_1199_eq, calc11_finishT_1204]
  · decide +kernel

theorem valid_inline_845 : Valid inline_845 := by
  rw [eq_inline_845]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_110
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_296
  subst c
  exact placed_valid 0 (4, 3) valid_511

theorem calc11_card_1205_eq : placed 1 (3, 5) card_22 = calc11_card_1205 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1206_eq : placed 1 (4, 5) card_74 = calc11_card_1206 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1207_eq : placed 0 (3, 1) card_325 = calc11_card_1207 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1208_eq : inline_845.required ∪ ∅ = calc11_set_1208 := by decide +kernel

theorem calc11_set_1209_eq : inline_845.envelope ∪ ∅ = calc11_set_1209 := by decide +kernel

theorem calc11_set_1210_eq : calc11_card_1207.required ∪ calc11_set_1208 = calc11_set_1210 := by decide +kernel

theorem calc11_set_1211_eq : calc11_card_1207.envelope ∪ calc11_set_1209 = calc11_set_1211 := by decide +kernel

theorem calc11_set_1212_eq : calc11_card_1206.required ∪ calc11_set_1210 = calc11_set_1212 := by decide +kernel

theorem calc11_set_1213_eq : calc11_card_1206.envelope ∪ calc11_set_1211 = calc11_set_1213 := by decide +kernel

theorem calc11_set_1214_eq : calc11_card_1205.required ∪ calc11_set_1212 = calc11_set_1214 := by decide +kernel

theorem calc11_set_1215_eq : calc11_card_1205.envelope ∪ calc11_set_1213 = calc11_set_1215 := by decide +kernel

theorem calc11_set_1216_eq : inline_845.envelope ∩ calc11_card_1205.envelope = calc11_set_1216 := by decide +kernel

theorem calc11_set_1217_eq : calc11_card_1207.envelope ∩ calc11_set_1216 = calc11_set_1217 := by decide +kernel

theorem calc11_set_1218_eq : calc11_card_1206.envelope ∩ calc11_set_1217 = calc11_set_1218 := by decide +kernel

theorem calc11_set_1219_eq : calc11_set_1214 ∪ calc11_set_1218 = calc11_set_1219 := by decide +kernel

theorem calc11_finishA_1220 : calc11_set_1219.erase (7, 5) = inline_846.required := by decide +kernel

theorem calc11_finishT_1220 : insert (7, 5) calc11_set_1215 = inline_846.envelope := by decide +kernel

theorem eq_inline_846 : inline_846 = combine (7, 5) [placed 1 (3, 5) card_22, placed 1 (4, 5) card_74, placed 0 (3, 1) card_325, inline_845] := by
  rw [calc11_card_1205_eq, calc11_card_1206_eq, calc11_card_1207_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1208_eq, calc11_set_1210_eq, calc11_set_1212_eq, calc11_set_1214_eq, calc11_set_1216_eq, calc11_set_1217_eq, calc11_set_1218_eq, calc11_set_1219_eq, calc11_finishA_1220]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1209_eq, calc11_set_1211_eq, calc11_set_1213_eq, calc11_set_1215_eq, calc11_finishT_1220]
  · decide +kernel

theorem valid_inline_846 : Valid inline_846 := by
  rw [eq_inline_846]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 5) valid_74
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_325
  subst c
  exact valid_inline_845

theorem calc11_card_1221_eq : placed 4 (7, 3) card_361 = calc11_card_1221 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1222_eq : placed 3 (8, 5) card_408 = calc11_card_1222 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1223_eq : placed 7 (8, 9) card_621 = calc11_card_1223 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1224_eq : placed 1 (0, 3) card_714 = calc11_card_1224 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1225_eq : inline_846.required ∪ ∅ = calc11_set_1225 := by decide +kernel

theorem calc11_set_1226_eq : inline_846.envelope ∪ ∅ = calc11_set_1226 := by decide +kernel

theorem calc11_set_1227_eq : calc11_card_1224.required ∪ calc11_set_1225 = calc11_set_1227 := by decide +kernel

theorem calc11_set_1228_eq : calc11_card_1224.envelope ∪ calc11_set_1226 = calc11_set_1228 := by decide +kernel

theorem calc11_set_1229_eq : calc11_card_1223.required ∪ calc11_set_1227 = calc11_set_1229 := by decide +kernel

theorem calc11_set_1230_eq : calc11_card_1223.envelope ∪ calc11_set_1228 = calc11_set_1230 := by decide +kernel

theorem calc11_set_1231_eq : calc11_card_1222.required ∪ calc11_set_1229 = calc11_set_1231 := by decide +kernel

theorem calc11_set_1232_eq : calc11_card_1222.envelope ∪ calc11_set_1230 = calc11_set_1232 := by decide +kernel

theorem calc11_set_1233_eq : calc11_card_1221.required ∪ calc11_set_1231 = calc11_set_1233 := by decide +kernel

theorem calc11_set_1234_eq : calc11_card_1221.envelope ∪ calc11_set_1232 = calc11_set_1234 := by decide +kernel

theorem calc11_set_1235_eq : inline_846.envelope ∩ calc11_card_1221.envelope = calc11_set_1235 := by decide +kernel

theorem calc11_set_1236_eq : calc11_card_1224.envelope ∩ calc11_set_1235 = calc11_set_1236 := by decide +kernel

theorem calc11_set_1237_eq : calc11_card_1223.envelope ∩ calc11_set_1236 = calc11_set_1237 := by decide +kernel

theorem calc11_set_1238_eq : calc11_card_1222.envelope ∩ calc11_set_1237 = calc11_set_1238 := by decide +kernel

theorem calc11_set_1239_eq : calc11_set_1233 ∪ calc11_set_1238 = calc11_set_1239 := by decide +kernel

theorem calc11_finishA_1240 : calc11_set_1239.erase (4, 6) = inline_847.required := by decide +kernel

theorem calc11_finishT_1240 : insert (4, 6) calc11_set_1234 = inline_847.envelope := by decide +kernel

theorem eq_inline_847 : inline_847 = combine (4, 6) [placed 4 (7, 3) card_361, placed 3 (8, 5) card_408, placed 7 (8, 9) card_621, placed 1 (0, 3) card_714, inline_846] := by
  rw [calc11_card_1221_eq, calc11_card_1222_eq, calc11_card_1223_eq, calc11_card_1224_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1225_eq, calc11_set_1227_eq, calc11_set_1229_eq, calc11_set_1231_eq, calc11_set_1233_eq, calc11_set_1235_eq, calc11_set_1236_eq, calc11_set_1237_eq, calc11_set_1238_eq, calc11_set_1239_eq, calc11_finishA_1240]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1226_eq, calc11_set_1228_eq, calc11_set_1230_eq, calc11_set_1232_eq, calc11_set_1234_eq, calc11_finishT_1240]
  · decide +kernel

theorem valid_inline_847 : Valid inline_847 := by
  rw [eq_inline_847]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_361
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_408
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 9) valid_621
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_714
  subst c
  exact valid_inline_846

theorem calc11_card_1241_eq : placed 2 (2, 9) card_523 = calc11_card_1241 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1242_eq : placed 1 (0, 3) card_532 = calc11_card_1242 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1243_eq : placed 6 (8, 9) card_536 = calc11_card_1243 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1244_eq : placed 6 (6, 10) card_545 = calc11_card_1244 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1245_eq : placed 2 (2, 10) card_655 = calc11_card_1245 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1246_eq : placed 1 (0, 1) card_664 = calc11_card_1246 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1247_eq : inline_847.required ∪ ∅ = calc11_set_1247 := by decide +kernel

theorem calc11_set_1248_eq : inline_847.envelope ∪ ∅ = calc11_set_1248 := by decide +kernel

theorem calc11_set_1249_eq : inline_844.required ∪ calc11_set_1247 = calc11_set_1249 := by decide +kernel

theorem calc11_set_1250_eq : inline_844.envelope ∪ calc11_set_1248 = calc11_set_1250 := by decide +kernel

theorem calc11_set_1251_eq : calc11_card_1246.required ∪ calc11_set_1249 = calc11_set_1251 := by decide +kernel

theorem calc11_set_1252_eq : calc11_card_1246.envelope ∪ calc11_set_1250 = calc11_set_1252 := by decide +kernel

theorem calc11_set_1253_eq : calc11_card_1245.required ∪ calc11_set_1251 = calc11_set_1253 := by decide +kernel

theorem calc11_set_1254_eq : calc11_card_1245.envelope ∪ calc11_set_1252 = calc11_set_1254 := by decide +kernel

theorem calc11_set_1255_eq : calc11_card_1244.required ∪ calc11_set_1253 = calc11_set_1255 := by decide +kernel

theorem calc11_set_1256_eq : calc11_card_1244.envelope ∪ calc11_set_1254 = calc11_set_1256 := by decide +kernel

theorem calc11_set_1257_eq : calc11_card_1243.required ∪ calc11_set_1255 = calc11_set_1257 := by decide +kernel

theorem calc11_set_1258_eq : calc11_card_1243.envelope ∪ calc11_set_1256 = calc11_set_1258 := by decide +kernel

theorem calc11_set_1259_eq : calc11_card_1242.required ∪ calc11_set_1257 = calc11_set_1259 := by decide +kernel

theorem calc11_set_1260_eq : calc11_card_1242.envelope ∪ calc11_set_1258 = calc11_set_1260 := by decide +kernel

theorem calc11_set_1261_eq : calc11_card_1241.required ∪ calc11_set_1259 = calc11_set_1261 := by decide +kernel

theorem calc11_set_1262_eq : calc11_card_1241.envelope ∪ calc11_set_1260 = calc11_set_1262 := by decide +kernel

theorem calc11_set_1263_eq : inline_847.envelope ∩ calc11_card_1241.envelope = calc11_set_1263 := by decide +kernel

theorem calc11_set_1264_eq : inline_844.envelope ∩ calc11_set_1263 = calc11_set_1264 := by decide +kernel

theorem calc11_set_1265_eq : calc11_card_1246.envelope ∩ calc11_set_1264 = calc11_set_1265 := by decide +kernel

theorem calc11_set_1266_eq : calc11_card_1245.envelope ∩ calc11_set_1265 = calc11_set_1266 := by decide +kernel

theorem calc11_set_1267_eq : calc11_card_1244.envelope ∩ calc11_set_1266 = calc11_set_1267 := by decide +kernel

theorem calc11_set_1268_eq : calc11_card_1243.envelope ∩ calc11_set_1267 = calc11_set_1268 := by decide +kernel

theorem calc11_set_1269_eq : calc11_card_1242.envelope ∩ calc11_set_1268 = calc11_set_1269 := by decide +kernel

theorem calc11_set_1270_eq : calc11_set_1261 ∪ calc11_set_1269 = calc11_set_1270 := by decide +kernel

theorem calc11_finishA_1271 : calc11_set_1270.erase (5, 6) = card_715.required := by decide +kernel

theorem calc11_finishT_1271 : insert (5, 6) calc11_set_1262 = card_715.envelope := by decide +kernel

theorem eq_card_715 : card_715 = combine (5, 6) [placed 2 (2, 9) card_523, placed 1 (0, 3) card_532, placed 6 (8, 9) card_536, placed 6 (6, 10) card_545, placed 2 (2, 10) card_655, placed 1 (0, 1) card_664, inline_844, inline_847] := by
  rw [calc11_card_1241_eq, calc11_card_1242_eq, calc11_card_1243_eq, calc11_card_1244_eq, calc11_card_1245_eq, calc11_card_1246_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1247_eq, calc11_set_1249_eq, calc11_set_1251_eq, calc11_set_1253_eq, calc11_set_1255_eq, calc11_set_1257_eq, calc11_set_1259_eq, calc11_set_1261_eq, calc11_set_1263_eq, calc11_set_1264_eq, calc11_set_1265_eq, calc11_set_1266_eq, calc11_set_1267_eq, calc11_set_1268_eq, calc11_set_1269_eq, calc11_set_1270_eq, calc11_finishA_1271]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1248_eq, calc11_set_1250_eq, calc11_set_1252_eq, calc11_set_1254_eq, calc11_set_1256_eq, calc11_set_1258_eq, calc11_set_1260_eq, calc11_set_1262_eq, calc11_finishT_1271]
  · decide +kernel

theorem valid_715 : Valid card_715 := by
  rw [eq_card_715]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_523
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_532
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_536
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 10) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_655
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_664
  rcases hc with rfl | hc
  · exact valid_inline_844
  subst c
  exact valid_inline_847


end OAI.Snaky21.Certificate

theorem solution : Valid card_715 ∧ True :=
  ⟨valid_715, True.intro⟩
