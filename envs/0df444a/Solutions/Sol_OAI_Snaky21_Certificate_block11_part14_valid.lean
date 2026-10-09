-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part14_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:18:17.835334+00:00
-- url     : https://prove2.me/submissions/ed1e1013-c710-4278-a198-489f2a81c00b

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Definitions.Def_Snaky21Calc11Part07
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part13_valid
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
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_120 : Valid card_120 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_155 : Valid card_155 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_229 : Valid card_229 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_232 : Valid card_232 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_276 : Valid card_276 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_315 : Valid card_315 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_317 : Valid card_317 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_329 : Valid card_329 := block05_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_338 : Valid card_338 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_341 : Valid card_341 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_377 : Valid card_377 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_437 : Valid card_437 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_452 : Valid card_452 := block07_valid.2.2.2.2.1
theorem valid_462 : Valid card_462 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_520 : Valid card_520 := block08_valid.2.2.2.2.2.2.2.2.1
theorem valid_587 : Valid card_587 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_611 : Valid card_611 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_612 : Valid card_612 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_633 : Valid card_633 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_640 : Valid card_640 := block10_valid.1
theorem valid_642 : Valid card_642 := block10_valid.2.2.1
theorem valid_643 : Valid card_643 := block10_valid.2.2.2.1

theorem calc11_card_1338_eq : placed 3 (8, 5) card_44 = calc11_card_1338 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1339_eq : placed 3 (8, 5) card_52 = calc11_card_1339 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1340_eq : placed 6 (8, 7) card_155 = calc11_card_1340 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1341_eq : placed 5 (2, 8) card_341 = calc11_card_1341 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1342_eq : calc11_card_1341.required ∪ ∅ = calc11_set_1342 := by decide +kernel

theorem calc11_set_1343_eq : calc11_card_1341.envelope ∪ ∅ = calc11_set_1343 := by decide +kernel

theorem calc11_set_1344_eq : calc11_card_1340.required ∪ calc11_set_1342 = calc11_set_1344 := by decide +kernel

theorem calc11_set_1345_eq : calc11_card_1340.envelope ∪ calc11_set_1343 = calc11_set_1345 := by decide +kernel

theorem calc11_set_1346_eq : calc11_card_1339.required ∪ calc11_set_1344 = calc11_set_1346 := by decide +kernel

theorem calc11_set_1347_eq : calc11_card_1339.envelope ∪ calc11_set_1345 = calc11_set_1347 := by decide +kernel

theorem calc11_set_1348_eq : calc11_card_1338.required ∪ calc11_set_1346 = calc11_set_1348 := by decide +kernel

theorem calc11_set_1349_eq : calc11_card_1338.envelope ∪ calc11_set_1347 = calc11_set_1349 := by decide +kernel

theorem calc11_set_1350_eq : calc11_card_1341.envelope ∩ calc11_card_1338.envelope = calc11_set_1350 := by decide +kernel

theorem calc11_set_1351_eq : calc11_card_1340.envelope ∩ calc11_set_1350 = calc11_set_1351 := by decide +kernel

theorem calc11_set_1352_eq : calc11_card_1339.envelope ∩ calc11_set_1351 = calc11_set_1352 := by decide +kernel

theorem calc11_set_1353_eq : calc11_set_1348 ∪ calc11_set_1352 = calc11_set_1353 := by decide +kernel

theorem calc11_finishA_1354 : calc11_set_1353.erase (6, 5) = inline_849.required := by decide +kernel

theorem calc11_finishT_1354 : insert (6, 5) calc11_set_1349 = inline_849.envelope := by decide +kernel

theorem eq_inline_849 : inline_849 = combine (6, 5) [placed 3 (8, 5) card_44, placed 3 (8, 5) card_52, placed 6 (8, 7) card_155, placed 5 (2, 8) card_341] := by
  rw [calc11_card_1338_eq, calc11_card_1339_eq, calc11_card_1340_eq, calc11_card_1341_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1342_eq, calc11_set_1344_eq, calc11_set_1346_eq, calc11_set_1348_eq, calc11_set_1350_eq, calc11_set_1351_eq, calc11_set_1352_eq, calc11_set_1353_eq, calc11_finishA_1354]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1343_eq, calc11_set_1345_eq, calc11_set_1347_eq, calc11_set_1349_eq, calc11_finishT_1354]
  · decide +kernel

theorem valid_inline_849 : Valid inline_849 := by
  rw [eq_inline_849]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 7) valid_155
  subst c
  exact placed_valid 5 (2, 8) valid_341

theorem calc11_card_1355_eq : placed 0 (2, 2) card_452 = calc11_card_1355 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1356_eq : placed 4 (10, 0) card_520 = calc11_card_1356 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1357_eq : placed 2 (5, 9) card_587 = calc11_card_1357 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1358_eq : placed 7 (8, 6) card_612 = calc11_card_1358 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1359_eq : placed 0 (2, 1) card_633 = calc11_card_1359 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1360_eq : calc11_card_1359.required ∪ ∅ = calc11_set_1360 := by decide +kernel

theorem calc11_set_1361_eq : calc11_card_1359.envelope ∪ ∅ = calc11_set_1361 := by decide +kernel

theorem calc11_set_1362_eq : calc11_card_1358.required ∪ calc11_set_1360 = calc11_set_1362 := by decide +kernel

theorem calc11_set_1363_eq : calc11_card_1358.envelope ∪ calc11_set_1361 = calc11_set_1363 := by decide +kernel

theorem calc11_set_1364_eq : calc11_card_1357.required ∪ calc11_set_1362 = calc11_set_1364 := by decide +kernel

theorem calc11_set_1365_eq : calc11_card_1357.envelope ∪ calc11_set_1363 = calc11_set_1365 := by decide +kernel

theorem calc11_set_1366_eq : calc11_card_1356.required ∪ calc11_set_1364 = calc11_set_1366 := by decide +kernel

theorem calc11_set_1367_eq : calc11_card_1356.envelope ∪ calc11_set_1365 = calc11_set_1367 := by decide +kernel

theorem calc11_set_1368_eq : calc11_card_1355.required ∪ calc11_set_1366 = calc11_set_1368 := by decide +kernel

theorem calc11_set_1369_eq : calc11_card_1355.envelope ∪ calc11_set_1367 = calc11_set_1369 := by decide +kernel

theorem calc11_set_1370_eq : calc11_card_1359.envelope ∩ calc11_card_1355.envelope = calc11_set_1370 := by decide +kernel

theorem calc11_set_1371_eq : calc11_card_1358.envelope ∩ calc11_set_1370 = calc11_set_1371 := by decide +kernel

theorem calc11_set_1372_eq : calc11_card_1357.envelope ∩ calc11_set_1371 = calc11_set_1372 := by decide +kernel

theorem calc11_set_1373_eq : calc11_card_1356.envelope ∩ calc11_set_1372 = calc11_set_1373 := by decide +kernel

theorem calc11_set_1374_eq : calc11_set_1368 ∪ calc11_set_1373 = calc11_set_1374 := by decide +kernel

theorem calc11_finishA_1375 : calc11_set_1374.erase (7, 6) = inline_850.required := by decide +kernel

theorem calc11_finishT_1375 : insert (7, 6) calc11_set_1369 = inline_850.envelope := by decide +kernel

theorem eq_inline_850 : inline_850 = combine (7, 6) [placed 0 (2, 2) card_452, placed 4 (10, 0) card_520, placed 2 (5, 9) card_587, placed 7 (8, 6) card_612, placed 0 (2, 1) card_633] := by
  rw [calc11_card_1355_eq, calc11_card_1356_eq, calc11_card_1357_eq, calc11_card_1358_eq, calc11_card_1359_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1360_eq, calc11_set_1362_eq, calc11_set_1364_eq, calc11_set_1366_eq, calc11_set_1368_eq, calc11_set_1370_eq, calc11_set_1371_eq, calc11_set_1372_eq, calc11_set_1373_eq, calc11_set_1374_eq, calc11_finishA_1375]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1361_eq, calc11_set_1363_eq, calc11_set_1365_eq, calc11_set_1367_eq, calc11_set_1369_eq, calc11_finishT_1375]
  · decide +kernel

theorem valid_inline_850 : Valid inline_850 := by
  rw [eq_inline_850]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 4 (10, 0) valid_520
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 9) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_612
  subst c
  exact placed_valid 0 (2, 1) valid_633

theorem calc11_card_1376_eq : placed 5 (4, 6) card_52 = calc11_card_1376 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1377_eq : placed 7 (8, 6) card_52 = calc11_card_1377 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1378_eq : placed 1 (4, 5) card_232 = calc11_card_1378 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1379_eq : placed 3 (8, 5) card_232 = calc11_card_1379 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1380_eq : calc11_card_1379.required ∪ ∅ = calc11_set_1380 := by decide +kernel

theorem calc11_set_1381_eq : calc11_card_1379.envelope ∪ ∅ = calc11_set_1381 := by decide +kernel

theorem calc11_set_1382_eq : calc11_card_1378.required ∪ calc11_set_1380 = calc11_set_1382 := by decide +kernel

theorem calc11_set_1383_eq : calc11_card_1378.envelope ∪ calc11_set_1381 = calc11_set_1383 := by decide +kernel

theorem calc11_set_1384_eq : calc11_card_1377.required ∪ calc11_set_1382 = calc11_set_1384 := by decide +kernel

theorem calc11_set_1385_eq : calc11_card_1377.envelope ∪ calc11_set_1383 = calc11_set_1385 := by decide +kernel

theorem calc11_set_1386_eq : calc11_card_1376.required ∪ calc11_set_1384 = calc11_set_1386 := by decide +kernel

theorem calc11_set_1387_eq : calc11_card_1376.envelope ∪ calc11_set_1385 = calc11_set_1387 := by decide +kernel

theorem calc11_set_1388_eq : calc11_card_1379.envelope ∩ calc11_card_1376.envelope = calc11_set_1388 := by decide +kernel

theorem calc11_set_1389_eq : calc11_card_1378.envelope ∩ calc11_set_1388 = calc11_set_1389 := by decide +kernel

theorem calc11_set_1390_eq : calc11_card_1377.envelope ∩ calc11_set_1389 = calc11_set_1390 := by decide +kernel

theorem calc11_set_1391_eq : calc11_set_1386 ∪ calc11_set_1390 = calc11_set_1391 := by decide +kernel

theorem calc11_finishA_1392 : calc11_set_1391.erase (6, 6) = inline_851.required := by decide +kernel

theorem calc11_finishT_1392 : insert (6, 6) calc11_set_1387 = inline_851.envelope := by decide +kernel

theorem eq_inline_851 : inline_851 = combine (6, 6) [placed 5 (4, 6) card_52, placed 7 (8, 6) card_52, placed 1 (4, 5) card_232, placed 3 (8, 5) card_232] := by
  rw [calc11_card_1376_eq, calc11_card_1377_eq, calc11_card_1378_eq, calc11_card_1379_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1380_eq, calc11_set_1382_eq, calc11_set_1384_eq, calc11_set_1386_eq, calc11_set_1388_eq, calc11_set_1389_eq, calc11_set_1390_eq, calc11_set_1391_eq, calc11_finishA_1392]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1381_eq, calc11_set_1383_eq, calc11_set_1385_eq, calc11_set_1387_eq, calc11_finishT_1392]
  · decide +kernel

theorem valid_inline_851 : Valid inline_851 := by
  rw [eq_inline_851]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 5) valid_232
  subst c
  exact placed_valid 3 (8, 5) valid_232

theorem calc11_card_1393_eq : placed 5 (6, 6) card_8 = calc11_card_1393 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1394_eq : placed 3 (9, 3) card_229 = calc11_card_1394 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1395_eq : calc11_card_1394.required ∪ ∅ = calc11_set_1395 := by decide +kernel

theorem calc11_set_1396_eq : calc11_card_1394.envelope ∪ ∅ = calc11_set_1396 := by decide +kernel

theorem calc11_set_1397_eq : calc11_card_1393.required ∪ calc11_set_1395 = calc11_set_1397 := by decide +kernel

theorem calc11_set_1398_eq : calc11_card_1393.envelope ∪ calc11_set_1396 = calc11_set_1398 := by decide +kernel

theorem calc11_set_1399_eq : calc11_card_1394.envelope ∩ calc11_card_1393.envelope = calc11_set_1399 := by decide +kernel

theorem calc11_set_1400_eq : calc11_set_1397 ∪ calc11_set_1399 = calc11_set_1400 := by decide +kernel

theorem calc11_finishA_1401 : calc11_set_1400.erase (7, 3) = inline_852.required := by decide +kernel

theorem calc11_finishT_1401 : insert (7, 3) calc11_set_1398 = inline_852.envelope := by decide +kernel

theorem eq_inline_852 : inline_852 = combine (7, 3) [placed 5 (6, 6) card_8, placed 3 (9, 3) card_229] := by
  rw [calc11_card_1393_eq, calc11_card_1394_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1395_eq, calc11_set_1397_eq, calc11_set_1399_eq, calc11_set_1400_eq, calc11_finishA_1401]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1396_eq, calc11_set_1398_eq, calc11_finishT_1401]
  · decide +kernel

theorem valid_inline_852 : Valid inline_852 := by
  rw [eq_inline_852]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (6, 6) valid_8
  subst c
  exact placed_valid 3 (9, 3) valid_229

theorem calc11_card_1402_eq : placed 2 (6, 8) card_12 = calc11_card_1402 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1403_eq : placed 6 (8, 8) card_12 = calc11_card_1403 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1404_eq : placed 0 (6, 2) card_12 = calc11_card_1404 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1405_eq : placed 4 (8, 3) card_377 = calc11_card_1405 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1406_eq : inline_852.required ∪ ∅ = calc11_set_1406 := by decide +kernel

theorem calc11_set_1407_eq : inline_852.envelope ∪ ∅ = calc11_set_1407 := by decide +kernel

theorem calc11_set_1408_eq : calc11_card_1405.required ∪ calc11_set_1406 = calc11_set_1408 := by decide +kernel

theorem calc11_set_1409_eq : calc11_card_1405.envelope ∪ calc11_set_1407 = calc11_set_1409 := by decide +kernel

theorem calc11_set_1410_eq : calc11_card_1404.required ∪ calc11_set_1408 = calc11_set_1410 := by decide +kernel

theorem calc11_set_1411_eq : calc11_card_1404.envelope ∪ calc11_set_1409 = calc11_set_1411 := by decide +kernel

theorem calc11_set_1412_eq : calc11_card_1403.required ∪ calc11_set_1410 = calc11_set_1412 := by decide +kernel

theorem calc11_set_1413_eq : calc11_card_1403.envelope ∪ calc11_set_1411 = calc11_set_1413 := by decide +kernel

theorem calc11_set_1414_eq : calc11_card_1402.required ∪ calc11_set_1412 = calc11_set_1414 := by decide +kernel

theorem calc11_set_1415_eq : calc11_card_1402.envelope ∪ calc11_set_1413 = calc11_set_1415 := by decide +kernel

theorem calc11_set_1416_eq : inline_852.envelope ∩ calc11_card_1402.envelope = calc11_set_1416 := by decide +kernel

theorem calc11_set_1417_eq : calc11_card_1405.envelope ∩ calc11_set_1416 = calc11_set_1417 := by decide +kernel

theorem calc11_set_1418_eq : calc11_card_1404.envelope ∩ calc11_set_1417 = calc11_set_1418 := by decide +kernel

theorem calc11_set_1419_eq : calc11_card_1403.envelope ∩ calc11_set_1418 = calc11_set_1419 := by decide +kernel

theorem calc11_set_1420_eq : calc11_set_1414 ∪ calc11_set_1419 = calc11_set_1420 := by decide +kernel

theorem calc11_finishA_1421 : calc11_set_1420.erase (7, 4) = inline_853.required := by decide +kernel

theorem calc11_finishT_1421 : insert (7, 4) calc11_set_1415 = inline_853.envelope := by decide +kernel

theorem eq_inline_853 : inline_853 = combine (7, 4) [placed 2 (6, 8) card_12, placed 6 (8, 8) card_12, placed 0 (6, 2) card_12, placed 4 (8, 3) card_377, inline_852] := by
  rw [calc11_card_1402_eq, calc11_card_1403_eq, calc11_card_1404_eq, calc11_card_1405_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1406_eq, calc11_set_1408_eq, calc11_set_1410_eq, calc11_set_1412_eq, calc11_set_1414_eq, calc11_set_1416_eq, calc11_set_1417_eq, calc11_set_1418_eq, calc11_set_1419_eq, calc11_set_1420_eq, calc11_finishA_1421]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1407_eq, calc11_set_1409_eq, calc11_set_1411_eq, calc11_set_1413_eq, calc11_set_1415_eq, calc11_finishT_1421]
  · decide +kernel

theorem valid_inline_853 : Valid inline_853 := by
  rw [eq_inline_853]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 8) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 8) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_377
  subst c
  exact valid_inline_852

theorem calc11_card_1422_eq : placed 3 (8, 5) card_315 = calc11_card_1422 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1423_eq : placed 0 (4, 2) card_317 = calc11_card_1423 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1424_eq : placed 2 (3, 9) card_640 = calc11_card_1424 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1425_eq : calc11_card_1424.required ∪ ∅ = calc11_set_1425 := by decide +kernel

theorem calc11_set_1426_eq : calc11_card_1424.envelope ∪ ∅ = calc11_set_1426 := by decide +kernel

theorem calc11_set_1427_eq : calc11_card_1423.required ∪ calc11_set_1425 = calc11_set_1427 := by decide +kernel

theorem calc11_set_1428_eq : calc11_card_1423.envelope ∪ calc11_set_1426 = calc11_set_1428 := by decide +kernel

theorem calc11_set_1429_eq : calc11_card_1422.required ∪ calc11_set_1427 = calc11_set_1429 := by decide +kernel

theorem calc11_set_1430_eq : calc11_card_1422.envelope ∪ calc11_set_1428 = calc11_set_1430 := by decide +kernel

theorem calc11_set_1431_eq : calc11_card_1424.envelope ∩ calc11_card_1422.envelope = calc11_set_1431 := by decide +kernel

theorem calc11_set_1432_eq : calc11_card_1423.envelope ∩ calc11_set_1431 = calc11_set_1432 := by decide +kernel

theorem calc11_set_1433_eq : calc11_set_1429 ∪ calc11_set_1432 = calc11_set_1433 := by decide +kernel

theorem calc11_finishA_1434 : calc11_set_1433.erase (6, 6) = inline_854.required := by decide +kernel

theorem calc11_finishT_1434 : insert (6, 6) calc11_set_1430 = inline_854.envelope := by decide +kernel

theorem eq_inline_854 : inline_854 = combine (6, 6) [placed 3 (8, 5) card_315, placed 0 (4, 2) card_317, placed 2 (3, 9) card_640] := by
  rw [calc11_card_1422_eq, calc11_card_1423_eq, calc11_card_1424_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1425_eq, calc11_set_1427_eq, calc11_set_1429_eq, calc11_set_1431_eq, calc11_set_1432_eq, calc11_set_1433_eq, calc11_finishA_1434]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1426_eq, calc11_set_1428_eq, calc11_set_1430_eq, calc11_finishT_1434]
  · decide +kernel

theorem valid_inline_854 : Valid inline_854 := by
  rw [eq_inline_854]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_315
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_317
  subst c
  exact placed_valid 2 (3, 9) valid_640

theorem calc11_card_1435_eq : placed 3 (10, 5) card_329 = calc11_card_1435 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1436_eq : placed 0 (2, 2) card_452 = calc11_card_1436 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1437_eq : placed 2 (6, 9) card_462 = calc11_card_1437 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1438_eq : inline_854.required ∪ ∅ = calc11_set_1438 := by decide +kernel

theorem calc11_set_1439_eq : inline_854.envelope ∪ ∅ = calc11_set_1439 := by decide +kernel

theorem calc11_set_1440_eq : inline_853.required ∪ calc11_set_1438 = calc11_set_1440 := by decide +kernel

theorem calc11_set_1441_eq : inline_853.envelope ∪ calc11_set_1439 = calc11_set_1441 := by decide +kernel

theorem calc11_set_1442_eq : inline_851.required ∪ calc11_set_1440 = calc11_set_1442 := by decide +kernel

theorem calc11_set_1443_eq : inline_851.envelope ∪ calc11_set_1441 = calc11_set_1443 := by decide +kernel

theorem calc11_set_1444_eq : calc11_card_1437.required ∪ calc11_set_1442 = calc11_set_1444 := by decide +kernel

theorem calc11_set_1445_eq : calc11_card_1437.envelope ∪ calc11_set_1443 = calc11_set_1445 := by decide +kernel

theorem calc11_set_1446_eq : calc11_card_1436.required ∪ calc11_set_1444 = calc11_set_1446 := by decide +kernel

theorem calc11_set_1447_eq : calc11_card_1436.envelope ∪ calc11_set_1445 = calc11_set_1447 := by decide +kernel

theorem calc11_set_1448_eq : calc11_card_1435.required ∪ calc11_set_1446 = calc11_set_1448 := by decide +kernel

theorem calc11_set_1449_eq : calc11_card_1435.envelope ∪ calc11_set_1447 = calc11_set_1449 := by decide +kernel

theorem calc11_set_1450_eq : inline_854.envelope ∩ calc11_card_1435.envelope = calc11_set_1450 := by decide +kernel

theorem calc11_set_1451_eq : inline_853.envelope ∩ calc11_set_1450 = calc11_set_1451 := by decide +kernel

theorem calc11_set_1452_eq : inline_851.envelope ∩ calc11_set_1451 = calc11_set_1452 := by decide +kernel

theorem calc11_set_1453_eq : calc11_card_1437.envelope ∩ calc11_set_1452 = calc11_set_1453 := by decide +kernel

theorem calc11_set_1454_eq : calc11_card_1436.envelope ∩ calc11_set_1453 = calc11_set_1454 := by decide +kernel

theorem calc11_set_1455_eq : calc11_set_1448 ∪ calc11_set_1454 = calc11_set_1455 := by decide +kernel

theorem calc11_finishA_1456 : calc11_set_1455.erase (7, 6) = inline_855.required := by decide +kernel

theorem calc11_finishT_1456 : insert (7, 6) calc11_set_1449 = inline_855.envelope := by decide +kernel

theorem eq_inline_855 : inline_855 = combine (7, 6) [placed 3 (10, 5) card_329, placed 0 (2, 2) card_452, placed 2 (6, 9) card_462, inline_851, inline_853, inline_854] := by
  rw [calc11_card_1435_eq, calc11_card_1436_eq, calc11_card_1437_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1438_eq, calc11_set_1440_eq, calc11_set_1442_eq, calc11_set_1444_eq, calc11_set_1446_eq, calc11_set_1448_eq, calc11_set_1450_eq, calc11_set_1451_eq, calc11_set_1452_eq, calc11_set_1453_eq, calc11_set_1454_eq, calc11_set_1455_eq, calc11_finishA_1456]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1439_eq, calc11_set_1441_eq, calc11_set_1443_eq, calc11_set_1445_eq, calc11_set_1447_eq, calc11_set_1449_eq, calc11_finishT_1456]
  · decide +kernel

theorem valid_inline_855 : Valid inline_855 := by
  rw [eq_inline_855]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 5) valid_329
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 9) valid_462
  rcases hc with rfl | hc
  · exact valid_inline_851
  rcases hc with rfl | hc
  · exact valid_inline_853
  subst c
  exact valid_inline_854

theorem calc11_card_1457_eq : placed 6 (8, 8) card_120 = calc11_card_1457 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1458_eq : placed 5 (2, 7) card_276 = calc11_card_1458 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1459_eq : placed 5 (2, 7) card_338 = calc11_card_1459 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1460_eq : placed 5 (2, 8) card_437 = calc11_card_1460 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1461_eq : placed 5 (1, 7) card_611 = calc11_card_1461 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1462_eq : placed 0 (4, 1) card_642 = calc11_card_1462 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1463_eq : placed 0 (4, 1) card_643 = calc11_card_1463 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1464_eq : inline_855.required ∪ ∅ = calc11_set_1464 := by decide +kernel

theorem calc11_set_1465_eq : inline_855.envelope ∪ ∅ = calc11_set_1465 := by decide +kernel

theorem calc11_set_1466_eq : inline_850.required ∪ calc11_set_1464 = calc11_set_1466 := by decide +kernel

theorem calc11_set_1467_eq : inline_850.envelope ∪ calc11_set_1465 = calc11_set_1467 := by decide +kernel

theorem calc11_set_1468_eq : inline_849.required ∪ calc11_set_1466 = calc11_set_1468 := by decide +kernel

theorem calc11_set_1469_eq : inline_849.envelope ∪ calc11_set_1467 = calc11_set_1469 := by decide +kernel

theorem calc11_set_1470_eq : calc11_card_1463.required ∪ calc11_set_1468 = calc11_set_1470 := by decide +kernel

theorem calc11_set_1471_eq : calc11_card_1463.envelope ∪ calc11_set_1469 = calc11_set_1471 := by decide +kernel

theorem calc11_set_1472_eq : calc11_card_1462.required ∪ calc11_set_1470 = calc11_set_1472 := by decide +kernel

theorem calc11_set_1473_eq : calc11_card_1462.envelope ∪ calc11_set_1471 = calc11_set_1473 := by decide +kernel

theorem calc11_set_1474_eq : calc11_card_1461.required ∪ calc11_set_1472 = calc11_set_1474 := by decide +kernel

theorem calc11_set_1475_eq : calc11_card_1461.envelope ∪ calc11_set_1473 = calc11_set_1475 := by decide +kernel

theorem calc11_set_1476_eq : calc11_card_1460.required ∪ calc11_set_1474 = calc11_set_1476 := by decide +kernel

theorem calc11_set_1477_eq : calc11_card_1460.envelope ∪ calc11_set_1475 = calc11_set_1477 := by decide +kernel

theorem calc11_set_1478_eq : calc11_card_1459.required ∪ calc11_set_1476 = calc11_set_1478 := by decide +kernel

theorem calc11_set_1479_eq : calc11_card_1459.envelope ∪ calc11_set_1477 = calc11_set_1479 := by decide +kernel

theorem calc11_set_1480_eq : calc11_card_1458.required ∪ calc11_set_1478 = calc11_set_1480 := by decide +kernel

theorem calc11_set_1481_eq : calc11_card_1458.envelope ∪ calc11_set_1479 = calc11_set_1481 := by decide +kernel

theorem calc11_set_1482_eq : calc11_card_1457.required ∪ calc11_set_1480 = calc11_set_1482 := by decide +kernel

theorem calc11_set_1483_eq : calc11_card_1457.envelope ∪ calc11_set_1481 = calc11_set_1483 := by decide +kernel

theorem calc11_set_1484_eq : inline_855.envelope ∩ calc11_card_1457.envelope = calc11_set_1484 := by decide +kernel

theorem calc11_set_1485_eq : inline_850.envelope ∩ calc11_set_1484 = calc11_set_1485 := by decide +kernel

theorem calc11_set_1486_eq : inline_849.envelope ∩ calc11_set_1485 = calc11_set_1486 := by decide +kernel

theorem calc11_set_1487_eq : calc11_card_1463.envelope ∩ calc11_set_1486 = calc11_set_1487 := by decide +kernel

theorem calc11_set_1488_eq : calc11_card_1462.envelope ∩ calc11_set_1487 = calc11_set_1488 := by decide +kernel

theorem calc11_set_1489_eq : calc11_card_1461.envelope ∩ calc11_set_1488 = calc11_set_1489 := by decide +kernel

theorem calc11_set_1490_eq : calc11_card_1460.envelope ∩ calc11_set_1489 = calc11_set_1490 := by decide +kernel

theorem calc11_set_1491_eq : calc11_card_1459.envelope ∩ calc11_set_1490 = calc11_set_1491 := by decide +kernel

theorem calc11_set_1492_eq : calc11_card_1458.envelope ∩ calc11_set_1491 = calc11_set_1492 := by decide +kernel

theorem calc11_set_1493_eq : calc11_set_1482 ∪ calc11_set_1492 = calc11_set_1493 := by decide +kernel

theorem calc11_finishA_1494 : calc11_set_1493.erase (7, 5) = card_718.required := by decide +kernel

theorem calc11_finishT_1494 : insert (7, 5) calc11_set_1483 = card_718.envelope := by decide +kernel

theorem eq_card_718 : card_718 = combine (7, 5) [placed 6 (8, 8) card_120, placed 5 (2, 7) card_276, placed 5 (2, 7) card_338, placed 5 (2, 8) card_437, placed 5 (1, 7) card_611, placed 0 (4, 1) card_642, placed 0 (4, 1) card_643, inline_849, inline_850, inline_855] := by
  rw [calc11_card_1457_eq, calc11_card_1458_eq, calc11_card_1459_eq, calc11_card_1460_eq, calc11_card_1461_eq, calc11_card_1462_eq, calc11_card_1463_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1464_eq, calc11_set_1466_eq, calc11_set_1468_eq, calc11_set_1470_eq, calc11_set_1472_eq, calc11_set_1474_eq, calc11_set_1476_eq, calc11_set_1478_eq, calc11_set_1480_eq, calc11_set_1482_eq, calc11_set_1484_eq, calc11_set_1485_eq, calc11_set_1486_eq, calc11_set_1487_eq, calc11_set_1488_eq, calc11_set_1489_eq, calc11_set_1490_eq, calc11_set_1491_eq, calc11_set_1492_eq, calc11_set_1493_eq, calc11_finishA_1494]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1465_eq, calc11_set_1467_eq, calc11_set_1469_eq, calc11_set_1471_eq, calc11_set_1473_eq, calc11_set_1475_eq, calc11_set_1477_eq, calc11_set_1479_eq, calc11_set_1481_eq, calc11_set_1483_eq, calc11_finishT_1494]
  · decide +kernel

theorem valid_718 : Valid card_718 := by
  rw [eq_card_718]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 8) valid_120
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_276
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_338
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_437
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_611
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_642
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_643
  rcases hc with rfl | hc
  · exact valid_inline_849
  rcases hc with rfl | hc
  · exact valid_inline_850
  subst c
  exact valid_inline_855


end OAI.Snaky21.Certificate

theorem solution : Valid card_718 ∧ True :=
  ⟨valid_718, True.intro⟩
