-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part13_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:17:34.737981+00:00
-- url     : https://prove2.me/submissions/dc84a6d7-415c-407d-ae99-2153f141b936

import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Definitions.Def_Snaky21Calc11Part06
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part12_valid
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
theorem valid_192 : Valid card_192 := block03_valid.1
theorem valid_550 : Valid card_550 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_578 : Valid card_578 := block09_valid.2.2.1
theorem valid_622 : Valid card_622 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_716 : Valid card_716 := block11_part12_valid.1

theorem calc11_card_1297_eq : placed 1 (2, 5) card_192 = calc11_card_1297 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1298_eq : placed 7 (8, 7) card_192 = calc11_card_1298 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1299_eq : placed 4 (10, 1) card_550 = calc11_card_1299 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1300_eq : placed 2 (0, 11) card_550 = calc11_card_1300 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1301_eq : placed 0 (3, 3) card_578 = calc11_card_1301 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1302_eq : placed 6 (7, 9) card_578 = calc11_card_1302 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1303_eq : placed 1 (1, 3) card_622 = calc11_card_1303 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1304_eq : placed 7 (9, 9) card_622 = calc11_card_1304 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1305_eq : placed 0 (0, 1) card_716 = calc11_card_1305 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1306_eq : placed 6 (10, 11) card_716 = calc11_card_1306 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1307_eq : calc11_card_1306.required ∪ ∅ = calc11_set_1307 := by decide +kernel

theorem calc11_set_1308_eq : calc11_card_1306.envelope ∪ ∅ = calc11_set_1308 := by decide +kernel

theorem calc11_set_1309_eq : calc11_card_1305.required ∪ calc11_set_1307 = calc11_set_1309 := by decide +kernel

theorem calc11_set_1310_eq : calc11_card_1305.envelope ∪ calc11_set_1308 = calc11_set_1310 := by decide +kernel

theorem calc11_set_1311_eq : calc11_card_1304.required ∪ calc11_set_1309 = calc11_set_1311 := by decide +kernel

theorem calc11_set_1312_eq : calc11_card_1304.envelope ∪ calc11_set_1310 = calc11_set_1312 := by decide +kernel

theorem calc11_set_1313_eq : calc11_card_1303.required ∪ calc11_set_1311 = calc11_set_1313 := by decide +kernel

theorem calc11_set_1314_eq : calc11_card_1303.envelope ∪ calc11_set_1312 = calc11_set_1314 := by decide +kernel

theorem calc11_set_1315_eq : calc11_card_1302.required ∪ calc11_set_1313 = calc11_set_1315 := by decide +kernel

theorem calc11_set_1316_eq : calc11_card_1302.envelope ∪ calc11_set_1314 = calc11_set_1316 := by decide +kernel

theorem calc11_set_1317_eq : calc11_card_1301.required ∪ calc11_set_1315 = calc11_set_1317 := by decide +kernel

theorem calc11_set_1318_eq : calc11_card_1301.envelope ∪ calc11_set_1316 = calc11_set_1318 := by decide +kernel

theorem calc11_set_1319_eq : calc11_card_1300.required ∪ calc11_set_1317 = calc11_set_1319 := by decide +kernel

theorem calc11_set_1320_eq : calc11_card_1300.envelope ∪ calc11_set_1318 = calc11_set_1320 := by decide +kernel

theorem calc11_set_1321_eq : calc11_card_1299.required ∪ calc11_set_1319 = calc11_set_1321 := by decide +kernel

theorem calc11_set_1322_eq : calc11_card_1299.envelope ∪ calc11_set_1320 = calc11_set_1322 := by decide +kernel

theorem calc11_set_1323_eq : calc11_card_1298.required ∪ calc11_set_1321 = calc11_set_1323 := by decide +kernel

theorem calc11_set_1324_eq : calc11_card_1298.envelope ∪ calc11_set_1322 = calc11_set_1324 := by decide +kernel

theorem calc11_set_1325_eq : calc11_card_1297.required ∪ calc11_set_1323 = calc11_set_1325 := by decide +kernel

theorem calc11_set_1326_eq : calc11_card_1297.envelope ∪ calc11_set_1324 = calc11_set_1326 := by decide +kernel

theorem calc11_set_1327_eq : calc11_card_1306.envelope ∩ calc11_card_1297.envelope = calc11_set_1327 := by decide +kernel

theorem calc11_set_1328_eq : calc11_card_1305.envelope ∩ calc11_set_1327 = calc11_set_1328 := by decide +kernel

theorem calc11_set_1329_eq : calc11_card_1304.envelope ∩ calc11_set_1328 = calc11_set_1329 := by decide +kernel

theorem calc11_set_1330_eq : calc11_card_1303.envelope ∩ calc11_set_1329 = calc11_set_1330 := by decide +kernel

theorem calc11_set_1331_eq : calc11_card_1302.envelope ∩ calc11_set_1330 = calc11_set_1331 := by decide +kernel

theorem calc11_set_1332_eq : calc11_card_1301.envelope ∩ calc11_set_1331 = calc11_set_1332 := by decide +kernel

theorem calc11_set_1333_eq : calc11_card_1300.envelope ∩ calc11_set_1332 = calc11_set_1333 := by decide +kernel

theorem calc11_set_1334_eq : calc11_card_1299.envelope ∩ calc11_set_1333 = calc11_set_1334 := by decide +kernel

theorem calc11_set_1335_eq : calc11_card_1298.envelope ∩ calc11_set_1334 = calc11_set_1335 := by decide +kernel

theorem calc11_set_1336_eq : calc11_set_1325 ∪ calc11_set_1335 = calc11_set_1336 := by decide +kernel

theorem calc11_finishA_1337 : calc11_set_1336.erase (6, 6) = card_717.required := by decide +kernel

theorem calc11_finishT_1337 : insert (6, 6) calc11_set_1326 = card_717.envelope := by decide +kernel

theorem eq_card_717 : card_717 = combine (6, 6) [placed 1 (2, 5) card_192, placed 7 (8, 7) card_192, placed 4 (10, 1) card_550, placed 2 (0, 11) card_550, placed 0 (3, 3) card_578, placed 6 (7, 9) card_578, placed 1 (1, 3) card_622, placed 7 (9, 9) card_622, placed 0 (0, 1) card_716, placed 6 (10, 11) card_716] := by
  rw [calc11_card_1297_eq, calc11_card_1298_eq, calc11_card_1299_eq, calc11_card_1300_eq, calc11_card_1301_eq, calc11_card_1302_eq, calc11_card_1303_eq, calc11_card_1304_eq, calc11_card_1305_eq, calc11_card_1306_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1307_eq, calc11_set_1309_eq, calc11_set_1311_eq, calc11_set_1313_eq, calc11_set_1315_eq, calc11_set_1317_eq, calc11_set_1319_eq, calc11_set_1321_eq, calc11_set_1323_eq, calc11_set_1325_eq, calc11_set_1327_eq, calc11_set_1328_eq, calc11_set_1329_eq, calc11_set_1330_eq, calc11_set_1331_eq, calc11_set_1332_eq, calc11_set_1333_eq, calc11_set_1334_eq, calc11_set_1335_eq, calc11_set_1336_eq, calc11_finishA_1337]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1308_eq, calc11_set_1310_eq, calc11_set_1312_eq, calc11_set_1314_eq, calc11_set_1316_eq, calc11_set_1318_eq, calc11_set_1320_eq, calc11_set_1322_eq, calc11_set_1324_eq, calc11_set_1326_eq, calc11_finishT_1337]
  · decide +kernel

theorem valid_717 : Valid card_717 := by
  rw [eq_card_717]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 4 (10, 1) valid_550
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 11) valid_550
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_578
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_578
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_622
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 9) valid_622
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_716
  subst c
  exact placed_valid 6 (10, 11) valid_716


end OAI.Snaky21.Certificate

theorem solution : Valid card_717 ∧ True :=
  ⟨valid_717, True.intro⟩
