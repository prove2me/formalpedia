-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:54:04.811767+00:00
-- url     : https://prove2.me/submissions/da948e16-3537-4495-9f6f-735995acddb6

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part01_valid
import Definitions.Def_Snaky21Calc11Part01
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part02_valid
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
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_33 : Valid card_33 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_115 : Valid card_115 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_116 : Valid card_116 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_118 : Valid card_118 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_134 : Valid card_134 := block02_valid.2.2.2.2.2.2.1
theorem valid_136 : Valid card_136 := block02_valid.2.2.2.2.2.2.2.2.1
theorem valid_180 : Valid card_180 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_267 : Valid card_267 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_302 : Valid card_302 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_303 : Valid card_303 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_322 : Valid card_322 := block05_valid.2.2.1
theorem valid_332 : Valid card_332 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_337 : Valid card_337 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_369 : Valid card_369 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_380 : Valid card_380 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_459 : Valid card_459 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_485 : Valid card_485 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_528 : Valid card_528 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_535 : Valid card_535 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_537 : Valid card_537 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_558 : Valid card_558 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_617 : Valid card_617 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_660 : Valid card_660 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_662 : Valid card_662 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_663 : Valid card_663 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_689 : Valid card_689 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_702 : Valid card_702 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_704 : Valid card_704 := block11_part00_valid.1
theorem valid_705 : Valid card_705 := block11_part01_valid.1
theorem valid_706 : Valid card_706 := block11_part02_valid.1

theorem calc11_card_363_eq : placed 5 (2, 8) card_116 = calc11_card_363 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_364_eq : placed 3 (7, 4) card_134 = calc11_card_364 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_365_eq : placed 3 (7, 4) card_180 = calc11_card_365 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_366_eq : placed 0 (4, 2) card_337 = calc11_card_366 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_367_eq : placed 3 (8, 4) card_435 = calc11_card_367 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_368_eq : placed 3 (7, 5) card_558 = calc11_card_368 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_369_eq : placed 1 (0, 3) card_662 = calc11_card_369 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_370_eq : calc11_card_369.required ∪ ∅ = calc11_set_370 := by decide +kernel

theorem calc11_set_371_eq : calc11_card_369.envelope ∪ ∅ = calc11_set_371 := by decide +kernel

theorem calc11_set_372_eq : calc11_card_368.required ∪ calc11_set_370 = calc11_set_372 := by decide +kernel

theorem calc11_set_373_eq : calc11_card_368.envelope ∪ calc11_set_371 = calc11_set_373 := by decide +kernel

theorem calc11_set_374_eq : calc11_card_367.required ∪ calc11_set_372 = calc11_set_374 := by decide +kernel

theorem calc11_set_375_eq : calc11_card_367.envelope ∪ calc11_set_373 = calc11_set_375 := by decide +kernel

theorem calc11_set_376_eq : calc11_card_366.required ∪ calc11_set_374 = calc11_set_376 := by decide +kernel

theorem calc11_set_377_eq : calc11_card_366.envelope ∪ calc11_set_375 = calc11_set_377 := by decide +kernel

theorem calc11_set_378_eq : calc11_card_365.required ∪ calc11_set_376 = calc11_set_378 := by decide +kernel

theorem calc11_set_379_eq : calc11_card_365.envelope ∪ calc11_set_377 = calc11_set_379 := by decide +kernel

theorem calc11_set_380_eq : calc11_card_364.required ∪ calc11_set_378 = calc11_set_380 := by decide +kernel

theorem calc11_set_381_eq : calc11_card_364.envelope ∪ calc11_set_379 = calc11_set_381 := by decide +kernel

theorem calc11_set_382_eq : calc11_card_363.required ∪ calc11_set_380 = calc11_set_382 := by decide +kernel

theorem calc11_set_383_eq : calc11_card_363.envelope ∪ calc11_set_381 = calc11_set_383 := by decide +kernel

theorem calc11_set_384_eq : calc11_card_369.envelope ∩ calc11_card_363.envelope = calc11_set_384 := by decide +kernel

theorem calc11_set_385_eq : calc11_card_368.envelope ∩ calc11_set_384 = calc11_set_385 := by decide +kernel

theorem calc11_set_386_eq : calc11_card_367.envelope ∩ calc11_set_385 = calc11_set_386 := by decide +kernel

theorem calc11_set_387_eq : calc11_card_366.envelope ∩ calc11_set_386 = calc11_set_387 := by decide +kernel

theorem calc11_set_388_eq : calc11_card_365.envelope ∩ calc11_set_387 = calc11_set_388 := by decide +kernel

theorem calc11_set_389_eq : calc11_card_364.envelope ∩ calc11_set_388 = calc11_set_389 := by decide +kernel

theorem calc11_set_390_eq : calc11_set_382 ∪ calc11_set_389 = calc11_set_390 := by decide +kernel

theorem calc11_finishA_391 : calc11_set_390.erase (5, 7) = inline_815.required := by decide +kernel

theorem calc11_finishT_391 : insert (5, 7) calc11_set_383 = inline_815.envelope := by decide +kernel

theorem eq_inline_815 : inline_815 = combine (5, 7) [placed 5 (2, 8) card_116, placed 3 (7, 4) card_134, placed 3 (7, 4) card_180, placed 0 (4, 2) card_337, placed 3 (8, 4) card_435, placed 3 (7, 5) card_558, placed 1 (0, 3) card_662] := by
  rw [calc11_card_363_eq, calc11_card_364_eq, calc11_card_365_eq, calc11_card_366_eq, calc11_card_367_eq, calc11_card_368_eq, calc11_card_369_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_370_eq, calc11_set_372_eq, calc11_set_374_eq, calc11_set_376_eq, calc11_set_378_eq, calc11_set_380_eq, calc11_set_382_eq, calc11_set_384_eq, calc11_set_385_eq, calc11_set_386_eq, calc11_set_387_eq, calc11_set_388_eq, calc11_set_389_eq, calc11_set_390_eq, calc11_finishA_391]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_371_eq, calc11_set_373_eq, calc11_set_375_eq, calc11_set_377_eq, calc11_set_379_eq, calc11_set_381_eq, calc11_set_383_eq, calc11_finishT_391]
  · decide +kernel

theorem valid_inline_815 : Valid inline_815 := by
  rw [eq_inline_815]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_337
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_558
  subst c
  exact placed_valid 1 (0, 3) valid_662

theorem calc11_card_392_eq : placed 0 (5, 3) card_7 = calc11_card_392 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_393_eq : placed 4 (6, 3) card_9 = calc11_card_393 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_394_eq : placed 3 (6, 4) card_380 = calc11_card_394 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_395_eq : calc11_card_394.required ∪ ∅ = calc11_set_395 := by decide +kernel

theorem calc11_set_396_eq : calc11_card_394.envelope ∪ ∅ = calc11_set_396 := by decide +kernel

theorem calc11_set_397_eq : calc11_card_393.required ∪ calc11_set_395 = calc11_set_397 := by decide +kernel

theorem calc11_set_398_eq : calc11_card_393.envelope ∪ calc11_set_396 = calc11_set_398 := by decide +kernel

theorem calc11_set_399_eq : calc11_card_392.required ∪ calc11_set_397 = calc11_set_399 := by decide +kernel

theorem calc11_set_400_eq : calc11_card_392.envelope ∪ calc11_set_398 = calc11_set_400 := by decide +kernel

theorem calc11_set_401_eq : calc11_card_394.envelope ∩ calc11_card_392.envelope = calc11_set_401 := by decide +kernel

theorem calc11_set_402_eq : calc11_card_393.envelope ∩ calc11_set_401 = calc11_set_402 := by decide +kernel

theorem calc11_set_403_eq : calc11_set_399 ∪ calc11_set_402 = calc11_set_403 := by decide +kernel

theorem calc11_finishA_404 : calc11_set_403.erase (5, 7) = inline_816.required := by decide +kernel

theorem calc11_finishT_404 : insert (5, 7) calc11_set_400 = inline_816.envelope := by decide +kernel

theorem eq_inline_816 : inline_816 = combine (5, 7) [placed 0 (5, 3) card_7, placed 4 (6, 3) card_9, placed 3 (6, 4) card_380] := by
  rw [calc11_card_392_eq, calc11_card_393_eq, calc11_card_394_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_395_eq, calc11_set_397_eq, calc11_set_399_eq, calc11_set_401_eq, calc11_set_402_eq, calc11_set_403_eq, calc11_finishA_404]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_396_eq, calc11_set_398_eq, calc11_set_400_eq, calc11_finishT_404]
  · decide +kernel

theorem valid_inline_816 : Valid inline_816 := by
  rw [eq_inline_816]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_9
  subst c
  exact placed_valid 3 (6, 4) valid_380

theorem calc11_card_405_eq : placed 6 (6, 8) card_14 = calc11_card_405 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_406_eq : placed 2 (4, 8) card_33 = calc11_card_406 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_407_eq : placed 5 (1, 7) card_322 = calc11_card_407 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_408_eq : inline_816.required ∪ ∅ = calc11_set_408 := by decide +kernel

theorem calc11_set_409_eq : inline_816.envelope ∪ ∅ = calc11_set_409 := by decide +kernel

theorem calc11_set_410_eq : calc11_card_407.required ∪ calc11_set_408 = calc11_set_410 := by decide +kernel

theorem calc11_set_411_eq : calc11_card_407.envelope ∪ calc11_set_409 = calc11_set_411 := by decide +kernel

theorem calc11_set_412_eq : calc11_card_406.required ∪ calc11_set_410 = calc11_set_412 := by decide +kernel

theorem calc11_set_413_eq : calc11_card_406.envelope ∪ calc11_set_411 = calc11_set_413 := by decide +kernel

theorem calc11_set_414_eq : calc11_card_405.required ∪ calc11_set_412 = calc11_set_414 := by decide +kernel

theorem calc11_set_415_eq : calc11_card_405.envelope ∪ calc11_set_413 = calc11_set_415 := by decide +kernel

theorem calc11_set_416_eq : inline_816.envelope ∩ calc11_card_405.envelope = calc11_set_416 := by decide +kernel

theorem calc11_set_417_eq : calc11_card_407.envelope ∩ calc11_set_416 = calc11_set_417 := by decide +kernel

theorem calc11_set_418_eq : calc11_card_406.envelope ∩ calc11_set_417 = calc11_set_418 := by decide +kernel

theorem calc11_set_419_eq : calc11_set_414 ∪ calc11_set_418 = calc11_set_419 := by decide +kernel

theorem calc11_finishA_420 : calc11_set_419.erase (5, 4) = inline_817.required := by decide +kernel

theorem calc11_finishT_420 : insert (5, 4) calc11_set_415 = inline_817.envelope := by decide +kernel

theorem eq_inline_817 : inline_817 = combine (5, 4) [placed 6 (6, 8) card_14, placed 2 (4, 8) card_33, placed 5 (1, 7) card_322, inline_816] := by
  rw [calc11_card_405_eq, calc11_card_406_eq, calc11_card_407_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_408_eq, calc11_set_410_eq, calc11_set_412_eq, calc11_set_414_eq, calc11_set_416_eq, calc11_set_417_eq, calc11_set_418_eq, calc11_set_419_eq, calc11_finishA_420]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_409_eq, calc11_set_411_eq, calc11_set_413_eq, calc11_set_415_eq, calc11_finishT_420]
  · decide +kernel

theorem valid_inline_817 : Valid inline_817 := by
  rw [eq_inline_817]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_322
  subst c
  exact valid_inline_816

theorem calc11_card_421_eq : placed 0 (5, 3) card_7 = calc11_card_421 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_422_eq : placed 1 (4, 4) card_8 = calc11_card_422 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_423_eq : placed 4 (6, 3) card_9 = calc11_card_423 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_424_eq : placed 2 (4, 9) card_485 = calc11_card_424 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_425_eq : calc11_card_424.required ∪ ∅ = calc11_set_425 := by decide +kernel

theorem calc11_set_426_eq : calc11_card_424.envelope ∪ ∅ = calc11_set_426 := by decide +kernel

theorem calc11_set_427_eq : calc11_card_423.required ∪ calc11_set_425 = calc11_set_427 := by decide +kernel

theorem calc11_set_428_eq : calc11_card_423.envelope ∪ calc11_set_426 = calc11_set_428 := by decide +kernel

theorem calc11_set_429_eq : calc11_card_422.required ∪ calc11_set_427 = calc11_set_429 := by decide +kernel

theorem calc11_set_430_eq : calc11_card_422.envelope ∪ calc11_set_428 = calc11_set_430 := by decide +kernel

theorem calc11_set_431_eq : calc11_card_421.required ∪ calc11_set_429 = calc11_set_431 := by decide +kernel

theorem calc11_set_432_eq : calc11_card_421.envelope ∪ calc11_set_430 = calc11_set_432 := by decide +kernel

theorem calc11_set_433_eq : calc11_card_424.envelope ∩ calc11_card_421.envelope = calc11_set_433 := by decide +kernel

theorem calc11_set_434_eq : calc11_card_423.envelope ∩ calc11_set_433 = calc11_set_434 := by decide +kernel

theorem calc11_set_435_eq : calc11_card_422.envelope ∩ calc11_set_434 = calc11_set_435 := by decide +kernel

theorem calc11_set_436_eq : calc11_set_431 ∪ calc11_set_435 = calc11_set_436 := by decide +kernel

theorem calc11_finishA_437 : calc11_set_436.erase (5, 7) = inline_818.required := by decide +kernel

theorem calc11_finishT_437 : insert (5, 7) calc11_set_432 = inline_818.envelope := by decide +kernel

theorem eq_inline_818 : inline_818 = combine (5, 7) [placed 0 (5, 3) card_7, placed 1 (4, 4) card_8, placed 4 (6, 3) card_9, placed 2 (4, 9) card_485] := by
  rw [calc11_card_421_eq, calc11_card_422_eq, calc11_card_423_eq, calc11_card_424_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_425_eq, calc11_set_427_eq, calc11_set_429_eq, calc11_set_431_eq, calc11_set_433_eq, calc11_set_434_eq, calc11_set_435_eq, calc11_set_436_eq, calc11_finishA_437]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_426_eq, calc11_set_428_eq, calc11_set_430_eq, calc11_set_432_eq, calc11_finishT_437]
  · decide +kernel

theorem valid_inline_818 : Valid inline_818 := by
  rw [eq_inline_818]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_9
  subst c
  exact placed_valid 2 (4, 9) valid_485

theorem calc11_card_438_eq : placed 2 (3, 7) card_136 = calc11_card_438 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_439_eq : placed 0 (3, 2) card_267 = calc11_card_439 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_440_eq : placed 5 (1, 7) card_322 = calc11_card_440 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_441_eq : placed 3 (9, 3) card_322 = calc11_card_441 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_442_eq : inline_818.required ∪ ∅ = calc11_set_442 := by decide +kernel

theorem calc11_set_443_eq : inline_818.envelope ∪ ∅ = calc11_set_443 := by decide +kernel

theorem calc11_set_444_eq : calc11_card_441.required ∪ calc11_set_442 = calc11_set_444 := by decide +kernel

theorem calc11_set_445_eq : calc11_card_441.envelope ∪ calc11_set_443 = calc11_set_445 := by decide +kernel

theorem calc11_set_446_eq : calc11_card_440.required ∪ calc11_set_444 = calc11_set_446 := by decide +kernel

theorem calc11_set_447_eq : calc11_card_440.envelope ∪ calc11_set_445 = calc11_set_447 := by decide +kernel

theorem calc11_set_448_eq : calc11_card_439.required ∪ calc11_set_446 = calc11_set_448 := by decide +kernel

theorem calc11_set_449_eq : calc11_card_439.envelope ∪ calc11_set_447 = calc11_set_449 := by decide +kernel

theorem calc11_set_450_eq : calc11_card_438.required ∪ calc11_set_448 = calc11_set_450 := by decide +kernel

theorem calc11_set_451_eq : calc11_card_438.envelope ∪ calc11_set_449 = calc11_set_451 := by decide +kernel

theorem calc11_set_452_eq : inline_818.envelope ∩ calc11_card_438.envelope = calc11_set_452 := by decide +kernel

theorem calc11_set_453_eq : calc11_card_441.envelope ∩ calc11_set_452 = calc11_set_453 := by decide +kernel

theorem calc11_set_454_eq : calc11_card_440.envelope ∩ calc11_set_453 = calc11_set_454 := by decide +kernel

theorem calc11_set_455_eq : calc11_card_439.envelope ∩ calc11_set_454 = calc11_set_455 := by decide +kernel

theorem calc11_set_456_eq : calc11_set_450 ∪ calc11_set_455 = calc11_set_456 := by decide +kernel

theorem calc11_finishA_457 : calc11_set_456.erase (5, 4) = inline_819.required := by decide +kernel

theorem calc11_finishT_457 : insert (5, 4) calc11_set_451 = inline_819.envelope := by decide +kernel

theorem eq_inline_819 : inline_819 = combine (5, 4) [placed 2 (3, 7) card_136, placed 0 (3, 2) card_267, placed 5 (1, 7) card_322, placed 3 (9, 3) card_322, inline_818] := by
  rw [calc11_card_438_eq, calc11_card_439_eq, calc11_card_440_eq, calc11_card_441_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_442_eq, calc11_set_444_eq, calc11_set_446_eq, calc11_set_448_eq, calc11_set_450_eq, calc11_set_452_eq, calc11_set_453_eq, calc11_set_454_eq, calc11_set_455_eq, calc11_set_456_eq, calc11_finishA_457]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_443_eq, calc11_set_445_eq, calc11_set_447_eq, calc11_set_449_eq, calc11_set_451_eq, calc11_finishT_457]
  · decide +kernel

theorem valid_inline_819 : Valid inline_819 := by
  rw [eq_inline_819]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_136
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_267
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 3) valid_322
  subst c
  exact valid_inline_818

theorem calc11_card_458_eq : placed 4 (6, 3) card_9 = calc11_card_458 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_459_eq : placed 1 (2, 4) card_115 = calc11_card_459 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_460_eq : placed 3 (8, 3) card_302 = calc11_card_460 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_461_eq : placed 3 (8, 3) card_303 = calc11_card_461 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_462_eq : calc11_card_461.required ∪ ∅ = calc11_set_462 := by decide +kernel

theorem calc11_set_463_eq : calc11_card_461.envelope ∪ ∅ = calc11_set_463 := by decide +kernel

theorem calc11_set_464_eq : calc11_card_460.required ∪ calc11_set_462 = calc11_set_464 := by decide +kernel

theorem calc11_set_465_eq : calc11_card_460.envelope ∪ calc11_set_463 = calc11_set_465 := by decide +kernel

theorem calc11_set_466_eq : calc11_card_459.required ∪ calc11_set_464 = calc11_set_466 := by decide +kernel

theorem calc11_set_467_eq : calc11_card_459.envelope ∪ calc11_set_465 = calc11_set_467 := by decide +kernel

theorem calc11_set_468_eq : calc11_card_458.required ∪ calc11_set_466 = calc11_set_468 := by decide +kernel

theorem calc11_set_469_eq : calc11_card_458.envelope ∪ calc11_set_467 = calc11_set_469 := by decide +kernel

theorem calc11_set_470_eq : calc11_card_461.envelope ∩ calc11_card_458.envelope = calc11_set_470 := by decide +kernel

theorem calc11_set_471_eq : calc11_card_460.envelope ∩ calc11_set_470 = calc11_set_471 := by decide +kernel

theorem calc11_set_472_eq : calc11_card_459.envelope ∩ calc11_set_471 = calc11_set_472 := by decide +kernel

theorem calc11_set_473_eq : calc11_set_468 ∪ calc11_set_472 = calc11_set_473 := by decide +kernel

theorem calc11_finishA_474 : calc11_set_473.erase (5, 7) = inline_820.required := by decide +kernel

theorem calc11_finishT_474 : insert (5, 7) calc11_set_469 = inline_820.envelope := by decide +kernel

theorem eq_inline_820 : inline_820 = combine (5, 7) [placed 4 (6, 3) card_9, placed 1 (2, 4) card_115, placed 3 (8, 3) card_302, placed 3 (8, 3) card_303] := by
  rw [calc11_card_458_eq, calc11_card_459_eq, calc11_card_460_eq, calc11_card_461_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_462_eq, calc11_set_464_eq, calc11_set_466_eq, calc11_set_468_eq, calc11_set_470_eq, calc11_set_471_eq, calc11_set_472_eq, calc11_set_473_eq, calc11_finishA_474]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_463_eq, calc11_set_465_eq, calc11_set_467_eq, calc11_set_469_eq, calc11_finishT_474]
  · decide +kernel

theorem valid_inline_820 : Valid inline_820 := by
  rw [eq_inline_820]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_302
  subst c
  exact placed_valid 3 (8, 3) valid_303

theorem calc11_card_475_eq : placed 2 (4, 8) card_13 = calc11_card_475 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_476_eq : placed 6 (6, 8) card_14 = calc11_card_476 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_477_eq : placed 7 (8, 7) card_332 = calc11_card_477 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_478_eq : inline_820.required ∪ ∅ = calc11_set_478 := by decide +kernel

theorem calc11_set_479_eq : inline_820.envelope ∪ ∅ = calc11_set_479 := by decide +kernel

theorem calc11_set_480_eq : calc11_card_477.required ∪ calc11_set_478 = calc11_set_480 := by decide +kernel

theorem calc11_set_481_eq : calc11_card_477.envelope ∪ calc11_set_479 = calc11_set_481 := by decide +kernel

theorem calc11_set_482_eq : calc11_card_476.required ∪ calc11_set_480 = calc11_set_482 := by decide +kernel

theorem calc11_set_483_eq : calc11_card_476.envelope ∪ calc11_set_481 = calc11_set_483 := by decide +kernel

theorem calc11_set_484_eq : calc11_card_475.required ∪ calc11_set_482 = calc11_set_484 := by decide +kernel

theorem calc11_set_485_eq : calc11_card_475.envelope ∪ calc11_set_483 = calc11_set_485 := by decide +kernel

theorem calc11_set_486_eq : inline_820.envelope ∩ calc11_card_475.envelope = calc11_set_486 := by decide +kernel

theorem calc11_set_487_eq : calc11_card_477.envelope ∩ calc11_set_486 = calc11_set_487 := by decide +kernel

theorem calc11_set_488_eq : calc11_card_476.envelope ∩ calc11_set_487 = calc11_set_488 := by decide +kernel

theorem calc11_set_489_eq : calc11_set_484 ∪ calc11_set_488 = calc11_set_489 := by decide +kernel

theorem calc11_finishA_490 : calc11_set_489.erase (5, 4) = inline_821.required := by decide +kernel

theorem calc11_finishT_490 : insert (5, 4) calc11_set_485 = inline_821.envelope := by decide +kernel

theorem eq_inline_821 : inline_821 = combine (5, 4) [placed 2 (4, 8) card_13, placed 6 (6, 8) card_14, placed 7 (8, 7) card_332, inline_820] := by
  rw [calc11_card_475_eq, calc11_card_476_eq, calc11_card_477_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_478_eq, calc11_set_480_eq, calc11_set_482_eq, calc11_set_484_eq, calc11_set_486_eq, calc11_set_487_eq, calc11_set_488_eq, calc11_set_489_eq, calc11_finishA_490]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_479_eq, calc11_set_481_eq, calc11_set_483_eq, calc11_set_485_eq, calc11_finishT_490]
  · decide +kernel

theorem valid_inline_821 : Valid inline_821 := by
  rw [eq_inline_821]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_332
  subst c
  exact valid_inline_820

theorem calc11_card_491_eq : placed 4 (6, 3) card_12 = calc11_card_491 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_492_eq : placed 4 (6, 3) card_13 = calc11_card_492 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_493_eq : placed 3 (8, 4) card_118 = calc11_card_493 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_494_eq : placed 6 (6, 10) card_369 = calc11_card_494 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_495_eq : placed 3 (8, 4) card_435 = calc11_card_495 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_496_eq : placed 0 (4, 1) card_528 = calc11_card_496 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_497_eq : placed 1 (1, 3) card_689 = calc11_card_497 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_498_eq : calc11_card_497.required ∪ ∅ = calc11_set_498 := by decide +kernel

theorem calc11_set_499_eq : calc11_card_497.envelope ∪ ∅ = calc11_set_499 := by decide +kernel

theorem calc11_set_500_eq : calc11_card_496.required ∪ calc11_set_498 = calc11_set_500 := by decide +kernel

theorem calc11_set_501_eq : calc11_card_496.envelope ∪ calc11_set_499 = calc11_set_501 := by decide +kernel

theorem calc11_set_502_eq : calc11_card_495.required ∪ calc11_set_500 = calc11_set_502 := by decide +kernel

theorem calc11_set_503_eq : calc11_card_495.envelope ∪ calc11_set_501 = calc11_set_503 := by decide +kernel

theorem calc11_set_504_eq : calc11_card_494.required ∪ calc11_set_502 = calc11_set_504 := by decide +kernel

theorem calc11_set_505_eq : calc11_card_494.envelope ∪ calc11_set_503 = calc11_set_505 := by decide +kernel

theorem calc11_set_506_eq : calc11_card_493.required ∪ calc11_set_504 = calc11_set_506 := by decide +kernel

theorem calc11_set_507_eq : calc11_card_493.envelope ∪ calc11_set_505 = calc11_set_507 := by decide +kernel

theorem calc11_set_508_eq : calc11_card_492.required ∪ calc11_set_506 = calc11_set_508 := by decide +kernel

theorem calc11_set_509_eq : calc11_card_492.envelope ∪ calc11_set_507 = calc11_set_509 := by decide +kernel

theorem calc11_set_510_eq : calc11_card_491.required ∪ calc11_set_508 = calc11_set_510 := by decide +kernel

theorem calc11_set_511_eq : calc11_card_491.envelope ∪ calc11_set_509 = calc11_set_511 := by decide +kernel

theorem calc11_set_512_eq : calc11_card_497.envelope ∩ calc11_card_491.envelope = calc11_set_512 := by decide +kernel

theorem calc11_set_513_eq : calc11_card_496.envelope ∩ calc11_set_512 = calc11_set_513 := by decide +kernel

theorem calc11_set_514_eq : calc11_card_495.envelope ∩ calc11_set_513 = calc11_set_514 := by decide +kernel

theorem calc11_set_515_eq : calc11_card_494.envelope ∩ calc11_set_514 = calc11_set_515 := by decide +kernel

theorem calc11_set_516_eq : calc11_card_493.envelope ∩ calc11_set_515 = calc11_set_516 := by decide +kernel

theorem calc11_set_517_eq : calc11_card_492.envelope ∩ calc11_set_516 = calc11_set_517 := by decide +kernel

theorem calc11_set_518_eq : calc11_set_510 ∪ calc11_set_517 = calc11_set_518 := by decide +kernel

theorem calc11_finishA_519 : calc11_set_518.erase (5, 7) = inline_822.required := by decide +kernel

theorem calc11_finishT_519 : insert (5, 7) calc11_set_511 = inline_822.envelope := by decide +kernel

theorem eq_inline_822 : inline_822 = combine (5, 7) [placed 4 (6, 3) card_12, placed 4 (6, 3) card_13, placed 3 (8, 4) card_118, placed 6 (6, 10) card_369, placed 3 (8, 4) card_435, placed 0 (4, 1) card_528, placed 1 (1, 3) card_689] := by
  rw [calc11_card_491_eq, calc11_card_492_eq, calc11_card_493_eq, calc11_card_494_eq, calc11_card_495_eq, calc11_card_496_eq, calc11_card_497_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_498_eq, calc11_set_500_eq, calc11_set_502_eq, calc11_set_504_eq, calc11_set_506_eq, calc11_set_508_eq, calc11_set_510_eq, calc11_set_512_eq, calc11_set_513_eq, calc11_set_514_eq, calc11_set_515_eq, calc11_set_516_eq, calc11_set_517_eq, calc11_set_518_eq, calc11_finishA_519]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_499_eq, calc11_set_501_eq, calc11_set_503_eq, calc11_set_505_eq, calc11_set_507_eq, calc11_set_509_eq, calc11_set_511_eq, calc11_finishT_519]
  · decide +kernel

theorem valid_inline_822 : Valid inline_822 := by
  rw [eq_inline_822]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 10) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_528
  subst c
  exact placed_valid 1 (1, 3) valid_689

theorem calc11_card_520_eq : placed 3 (8, 4) card_537 = calc11_card_520 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_521_eq : placed 2 (3, 9) card_537 = calc11_card_521 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_522_eq : placed 3 (7, 4) card_702 = calc11_card_522 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_523_eq : placed 2 (3, 8) card_702 = calc11_card_523 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_524_eq : placed 1 (0, 4) card_704 = calc11_card_524 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_525_eq : placed 0 (3, 1) card_704 = calc11_card_525 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_526_eq : calc11_card_525.required ∪ ∅ = calc11_set_526 := by decide +kernel

theorem calc11_set_527_eq : calc11_card_525.envelope ∪ ∅ = calc11_set_527 := by decide +kernel

theorem calc11_set_528_eq : calc11_card_524.required ∪ calc11_set_526 = calc11_set_528 := by decide +kernel

theorem calc11_set_529_eq : calc11_card_524.envelope ∪ calc11_set_527 = calc11_set_529 := by decide +kernel

theorem calc11_set_530_eq : calc11_card_523.required ∪ calc11_set_528 = calc11_set_530 := by decide +kernel

theorem calc11_set_531_eq : calc11_card_523.envelope ∪ calc11_set_529 = calc11_set_531 := by decide +kernel

theorem calc11_set_532_eq : calc11_card_522.required ∪ calc11_set_530 = calc11_set_532 := by decide +kernel

theorem calc11_set_533_eq : calc11_card_522.envelope ∪ calc11_set_531 = calc11_set_533 := by decide +kernel

theorem calc11_set_534_eq : calc11_card_521.required ∪ calc11_set_532 = calc11_set_534 := by decide +kernel

theorem calc11_set_535_eq : calc11_card_521.envelope ∪ calc11_set_533 = calc11_set_535 := by decide +kernel

theorem calc11_set_536_eq : calc11_card_520.required ∪ calc11_set_534 = calc11_set_536 := by decide +kernel

theorem calc11_set_537_eq : calc11_card_520.envelope ∪ calc11_set_535 = calc11_set_537 := by decide +kernel

theorem calc11_set_538_eq : calc11_card_525.envelope ∩ calc11_card_520.envelope = calc11_set_538 := by decide +kernel

theorem calc11_set_539_eq : calc11_card_524.envelope ∩ calc11_set_538 = calc11_set_539 := by decide +kernel

theorem calc11_set_540_eq : calc11_card_523.envelope ∩ calc11_set_539 = calc11_set_540 := by decide +kernel

theorem calc11_set_541_eq : calc11_card_522.envelope ∩ calc11_set_540 = calc11_set_541 := by decide +kernel

theorem calc11_set_542_eq : calc11_card_521.envelope ∩ calc11_set_541 = calc11_set_542 := by decide +kernel

theorem calc11_set_543_eq : calc11_set_536 ∪ calc11_set_542 = calc11_set_543 := by decide +kernel

theorem calc11_finishA_544 : calc11_set_543.erase (4, 6) = inline_823.required := by decide +kernel

theorem calc11_finishT_544 : insert (4, 6) calc11_set_537 = inline_823.envelope := by decide +kernel

theorem eq_inline_823 : inline_823 = combine (4, 6) [placed 3 (8, 4) card_537, placed 2 (3, 9) card_537, placed 3 (7, 4) card_702, placed 2 (3, 8) card_702, placed 1 (0, 4) card_704, placed 0 (3, 1) card_704] := by
  rw [calc11_card_520_eq, calc11_card_521_eq, calc11_card_522_eq, calc11_card_523_eq, calc11_card_524_eq, calc11_card_525_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_526_eq, calc11_set_528_eq, calc11_set_530_eq, calc11_set_532_eq, calc11_set_534_eq, calc11_set_536_eq, calc11_set_538_eq, calc11_set_539_eq, calc11_set_540_eq, calc11_set_541_eq, calc11_set_542_eq, calc11_set_543_eq, calc11_finishA_544]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_527_eq, calc11_set_529_eq, calc11_set_531_eq, calc11_set_533_eq, calc11_set_535_eq, calc11_set_537_eq, calc11_finishT_544]
  · decide +kernel

theorem valid_inline_823 : Valid inline_823 := by
  rw [eq_inline_823]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_537
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_537
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_702
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_702
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_704
  subst c
  exact placed_valid 0 (3, 1) valid_704

theorem calc11_card_545_eq : placed 0 (4, 1) card_459 = calc11_card_545 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_546_eq : placed 2 (3, 10) card_535 = calc11_card_546 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_547_eq : placed 0 (1, 1) card_617 = calc11_card_547 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_548_eq : placed 1 (0, 1) card_660 = calc11_card_548 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_549_eq : placed 1 (0, 3) card_663 = calc11_card_549 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_550_eq : placed 2 (2, 10) card_705 = calc11_card_550 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_551_eq : placed 2 (0, 10) card_706 = calc11_card_551 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_552_eq : calc11_card_551.required ∪ ∅ = calc11_set_552 := by decide +kernel

theorem calc11_set_553_eq : calc11_card_551.envelope ∪ ∅ = calc11_set_553 := by decide +kernel

theorem calc11_set_554_eq : calc11_card_550.required ∪ calc11_set_552 = calc11_set_554 := by decide +kernel

theorem calc11_set_555_eq : calc11_card_550.envelope ∪ calc11_set_553 = calc11_set_555 := by decide +kernel

theorem calc11_set_556_eq : inline_823.required ∪ calc11_set_554 = calc11_set_556 := by decide +kernel

theorem calc11_set_557_eq : inline_823.envelope ∪ calc11_set_555 = calc11_set_557 := by decide +kernel

theorem calc11_set_558_eq : inline_822.required ∪ calc11_set_556 = calc11_set_558 := by decide +kernel

theorem calc11_set_559_eq : inline_822.envelope ∪ calc11_set_557 = calc11_set_559 := by decide +kernel

theorem calc11_set_560_eq : inline_821.required ∪ calc11_set_558 = calc11_set_560 := by decide +kernel

theorem calc11_set_561_eq : inline_821.envelope ∪ calc11_set_559 = calc11_set_561 := by decide +kernel

theorem calc11_set_562_eq : inline_819.required ∪ calc11_set_560 = calc11_set_562 := by decide +kernel

theorem calc11_set_563_eq : inline_819.envelope ∪ calc11_set_561 = calc11_set_563 := by decide +kernel

theorem calc11_set_564_eq : inline_817.required ∪ calc11_set_562 = calc11_set_564 := by decide +kernel

theorem calc11_set_565_eq : inline_817.envelope ∪ calc11_set_563 = calc11_set_565 := by decide +kernel

theorem calc11_set_566_eq : inline_815.required ∪ calc11_set_564 = calc11_set_566 := by decide +kernel

theorem calc11_set_567_eq : inline_815.envelope ∪ calc11_set_565 = calc11_set_567 := by decide +kernel

theorem calc11_set_568_eq : calc11_card_549.required ∪ calc11_set_566 = calc11_set_568 := by decide +kernel

theorem calc11_set_569_eq : calc11_card_549.envelope ∪ calc11_set_567 = calc11_set_569 := by decide +kernel

theorem calc11_set_570_eq : calc11_card_548.required ∪ calc11_set_568 = calc11_set_570 := by decide +kernel

theorem calc11_set_571_eq : calc11_card_548.envelope ∪ calc11_set_569 = calc11_set_571 := by decide +kernel

theorem calc11_set_572_eq : calc11_card_547.required ∪ calc11_set_570 = calc11_set_572 := by decide +kernel

theorem calc11_set_573_eq : calc11_card_547.envelope ∪ calc11_set_571 = calc11_set_573 := by decide +kernel

theorem calc11_set_574_eq : calc11_card_546.required ∪ calc11_set_572 = calc11_set_574 := by decide +kernel

theorem calc11_set_575_eq : calc11_card_546.envelope ∪ calc11_set_573 = calc11_set_575 := by decide +kernel

theorem calc11_set_576_eq : calc11_card_545.required ∪ calc11_set_574 = calc11_set_576 := by decide +kernel

theorem calc11_set_577_eq : calc11_card_545.envelope ∪ calc11_set_575 = calc11_set_577 := by decide +kernel

theorem calc11_set_578_eq : calc11_card_551.envelope ∩ calc11_card_545.envelope = calc11_set_578 := by decide +kernel

theorem calc11_set_579_eq : calc11_card_550.envelope ∩ calc11_set_578 = calc11_set_579 := by decide +kernel

theorem calc11_set_580_eq : inline_823.envelope ∩ calc11_set_579 = calc11_set_580 := by decide +kernel

theorem calc11_set_581_eq : inline_822.envelope ∩ calc11_set_580 = calc11_set_581 := by decide +kernel

theorem calc11_set_582_eq : inline_821.envelope ∩ calc11_set_581 = calc11_set_582 := by decide +kernel

theorem calc11_set_583_eq : inline_819.envelope ∩ calc11_set_582 = calc11_set_583 := by decide +kernel

theorem calc11_set_584_eq : inline_817.envelope ∩ calc11_set_583 = calc11_set_584 := by decide +kernel

theorem calc11_set_585_eq : inline_815.envelope ∩ calc11_set_584 = calc11_set_585 := by decide +kernel

theorem calc11_set_586_eq : calc11_card_549.envelope ∩ calc11_set_585 = calc11_set_586 := by decide +kernel

theorem calc11_set_587_eq : calc11_card_548.envelope ∩ calc11_set_586 = calc11_set_587 := by decide +kernel

theorem calc11_set_588_eq : calc11_card_547.envelope ∩ calc11_set_587 = calc11_set_588 := by decide +kernel

theorem calc11_set_589_eq : calc11_card_546.envelope ∩ calc11_set_588 = calc11_set_589 := by decide +kernel

theorem calc11_set_590_eq : calc11_set_576 ∪ calc11_set_589 = calc11_set_590 := by decide +kernel

theorem calc11_finishA_591 : calc11_set_590.erase (5, 6) = card_707.required := by decide +kernel

theorem calc11_finishT_591 : insert (5, 6) calc11_set_577 = card_707.envelope := by decide +kernel

theorem eq_card_707 : card_707 = combine (5, 6) [placed 0 (4, 1) card_459, placed 2 (3, 10) card_535, placed 0 (1, 1) card_617, placed 1 (0, 1) card_660, placed 1 (0, 3) card_663, inline_815, inline_817, inline_819, inline_821, inline_822, inline_823, placed 2 (2, 10) card_705, placed 2 (0, 10) card_706] := by
  rw [calc11_card_545_eq, calc11_card_546_eq, calc11_card_547_eq, calc11_card_548_eq, calc11_card_549_eq, calc11_card_550_eq, calc11_card_551_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_552_eq, calc11_set_554_eq, calc11_set_556_eq, calc11_set_558_eq, calc11_set_560_eq, calc11_set_562_eq, calc11_set_564_eq, calc11_set_566_eq, calc11_set_568_eq, calc11_set_570_eq, calc11_set_572_eq, calc11_set_574_eq, calc11_set_576_eq, calc11_set_578_eq, calc11_set_579_eq, calc11_set_580_eq, calc11_set_581_eq, calc11_set_582_eq, calc11_set_583_eq, calc11_set_584_eq, calc11_set_585_eq, calc11_set_586_eq, calc11_set_587_eq, calc11_set_588_eq, calc11_set_589_eq, calc11_set_590_eq, calc11_finishA_591]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_553_eq, calc11_set_555_eq, calc11_set_557_eq, calc11_set_559_eq, calc11_set_561_eq, calc11_set_563_eq, calc11_set_565_eq, calc11_set_567_eq, calc11_set_569_eq, calc11_set_571_eq, calc11_set_573_eq, calc11_set_575_eq, calc11_set_577_eq, calc11_finishT_591]
  · decide +kernel

theorem valid_707 : Valid card_707 := by
  rw [eq_card_707]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 10) valid_535
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_617
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_660
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_663
  rcases hc with rfl | hc
  · exact valid_inline_815
  rcases hc with rfl | hc
  · exact valid_inline_817
  rcases hc with rfl | hc
  · exact valid_inline_819
  rcases hc with rfl | hc
  · exact valid_inline_821
  rcases hc with rfl | hc
  · exact valid_inline_822
  rcases hc with rfl | hc
  · exact valid_inline_823
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_705
  subst c
  exact placed_valid 2 (0, 10) valid_706


end OAI.Snaky21.Certificate

theorem solution : Valid card_707 ∧ True :=
  ⟨valid_707, True.intro⟩
