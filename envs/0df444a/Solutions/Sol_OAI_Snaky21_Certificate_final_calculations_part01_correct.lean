-- Prove2me | solution 1 for OAI.Snaky21.Certificate.final_calculations_part01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:33:51.168009+00:00
-- url     : https://prove2.me/submissions/44f8c27a-204d-4fad-a9c0-1d1733b67329

import Definitions.Def_Snaky21Calc11Part11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

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

theorem calc11_card_2315_eq : placed 4 (13, 3) card_713 = calc11_card_2315 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2316_eq : placed 5 (3, 13) card_713 = calc11_card_2316 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2317_eq : placed 2 (3, 13) card_713 = calc11_card_2317 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2318_eq : placed 3 (13, 3) card_713 = calc11_card_2318 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2319_eq : placed 0 (1, 1) card_725 = calc11_card_2319 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2320_eq : placed 1 (1, 1) card_725 = calc11_card_2320 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2321_eq : placed 4 (15, 1) card_725 = calc11_card_2321 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2322_eq : placed 5 (1, 15) card_725 = calc11_card_2322 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2323_eq : placed 2 (1, 15) card_725 = calc11_card_2323 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2324_eq : placed 3 (15, 1) card_725 = calc11_card_2324 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2325_eq : placed 6 (15, 15) card_725 = calc11_card_2325 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2326_eq : placed 7 (15, 15) card_725 = calc11_card_2326 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2327_eq : placed 1 (1, 1) card_726 = calc11_card_2327 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2328_eq : placed 4 (15, 1) card_726 = calc11_card_2328 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2329_eq : placed 2 (1, 15) card_726 = calc11_card_2329 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2330_eq : placed 6 (15, 15) card_726 = calc11_card_2330 := by
  apply computed_card_ext <;> decide +kernel
end OAI.Snaky21.Certificate

theorem solution : (placed 4 (13, 3) card_713 = calc11_card_2315) ∧ (placed 5 (3, 13) card_713 = calc11_card_2316) ∧ (placed 2 (3, 13) card_713 = calc11_card_2317) ∧ (placed 3 (13, 3) card_713 = calc11_card_2318) ∧ (placed 0 (1, 1) card_725 = calc11_card_2319) ∧ (placed 1 (1, 1) card_725 = calc11_card_2320) ∧ (placed 4 (15, 1) card_725 = calc11_card_2321) ∧ (placed 5 (1, 15) card_725 = calc11_card_2322) ∧ (placed 2 (1, 15) card_725 = calc11_card_2323) ∧ (placed 3 (15, 1) card_725 = calc11_card_2324) ∧ (placed 6 (15, 15) card_725 = calc11_card_2325) ∧ (placed 7 (15, 15) card_725 = calc11_card_2326) ∧ (placed 1 (1, 1) card_726 = calc11_card_2327) ∧ (placed 4 (15, 1) card_726 = calc11_card_2328) ∧ (placed 2 (1, 15) card_726 = calc11_card_2329) ∧ (placed 6 (15, 15) card_726 = calc11_card_2330) ∧ True :=
  ⟨calc11_card_2315_eq, calc11_card_2316_eq, calc11_card_2317_eq, calc11_card_2318_eq, calc11_card_2319_eq, calc11_card_2320_eq, calc11_card_2321_eq, calc11_card_2322_eq, calc11_card_2323_eq, calc11_card_2324_eq, calc11_card_2325_eq, calc11_card_2326_eq, calc11_card_2327_eq, calc11_card_2328_eq, calc11_card_2329_eq, calc11_card_2330_eq, True.intro⟩
