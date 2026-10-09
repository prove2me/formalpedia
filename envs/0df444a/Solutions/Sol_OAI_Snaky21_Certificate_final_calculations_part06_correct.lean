-- Prove2me | solution 1 for OAI.Snaky21.Certificate.final_calculations_part06_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:47:34.772128+00:00
-- url     : https://prove2.me/submissions/7bb95c13-9e10-45ff-a81f-633a9b3fa2aa

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

theorem calc11_set_2395_eq : calc11_card_2330.envelope ∩ calc11_card_2299.envelope = calc11_set_2395 := by decide +kernel
theorem calc11_set_2396_eq : calc11_card_2329.envelope ∩ calc11_set_2395 = calc11_set_2396 := by decide +kernel
theorem calc11_set_2397_eq : calc11_card_2328.envelope ∩ calc11_set_2396 = calc11_set_2397 := by decide +kernel
theorem calc11_set_2398_eq : calc11_card_2327.envelope ∩ calc11_set_2397 = calc11_set_2398 := by decide +kernel
theorem calc11_set_2399_eq : calc11_card_2326.envelope ∩ calc11_set_2398 = calc11_set_2399 := by decide +kernel
theorem calc11_set_2400_eq : calc11_card_2325.envelope ∩ calc11_set_2399 = calc11_set_2400 := by decide +kernel
theorem calc11_set_2401_eq : calc11_card_2324.envelope ∩ calc11_set_2400 = calc11_set_2401 := by decide +kernel
theorem calc11_set_2402_eq : calc11_card_2323.envelope ∩ calc11_set_2401 = calc11_set_2402 := by decide +kernel
theorem calc11_set_2403_eq : calc11_card_2322.envelope ∩ calc11_set_2402 = calc11_set_2403 := by decide +kernel
theorem calc11_set_2404_eq : calc11_card_2321.envelope ∩ calc11_set_2403 = calc11_set_2404 := by decide +kernel
theorem calc11_set_2405_eq : calc11_card_2320.envelope ∩ calc11_set_2404 = calc11_set_2405 := by decide +kernel
theorem calc11_set_2406_eq : calc11_card_2319.envelope ∩ calc11_set_2405 = calc11_set_2406 := by decide +kernel
theorem calc11_set_2407_eq : calc11_card_2318.envelope ∩ calc11_set_2406 = calc11_set_2407 := by decide +kernel
theorem calc11_set_2408_eq : calc11_card_2317.envelope ∩ calc11_set_2407 = calc11_set_2408 := by decide +kernel
theorem calc11_set_2409_eq : calc11_card_2316.envelope ∩ calc11_set_2408 = calc11_set_2409 := by decide +kernel
theorem calc11_set_2410_eq : calc11_card_2315.envelope ∩ calc11_set_2409 = calc11_set_2410 := by decide +kernel
end OAI.Snaky21.Certificate

theorem solution : (calc11_card_2330.envelope ∩ calc11_card_2299.envelope = calc11_set_2395) ∧ (calc11_card_2329.envelope ∩ calc11_set_2395 = calc11_set_2396) ∧ (calc11_card_2328.envelope ∩ calc11_set_2396 = calc11_set_2397) ∧ (calc11_card_2327.envelope ∩ calc11_set_2397 = calc11_set_2398) ∧ (calc11_card_2326.envelope ∩ calc11_set_2398 = calc11_set_2399) ∧ (calc11_card_2325.envelope ∩ calc11_set_2399 = calc11_set_2400) ∧ (calc11_card_2324.envelope ∩ calc11_set_2400 = calc11_set_2401) ∧ (calc11_card_2323.envelope ∩ calc11_set_2401 = calc11_set_2402) ∧ (calc11_card_2322.envelope ∩ calc11_set_2402 = calc11_set_2403) ∧ (calc11_card_2321.envelope ∩ calc11_set_2403 = calc11_set_2404) ∧ (calc11_card_2320.envelope ∩ calc11_set_2404 = calc11_set_2405) ∧ (calc11_card_2319.envelope ∩ calc11_set_2405 = calc11_set_2406) ∧ (calc11_card_2318.envelope ∩ calc11_set_2406 = calc11_set_2407) ∧ (calc11_card_2317.envelope ∩ calc11_set_2407 = calc11_set_2408) ∧ (calc11_card_2316.envelope ∩ calc11_set_2408 = calc11_set_2409) ∧ (calc11_card_2315.envelope ∩ calc11_set_2409 = calc11_set_2410) ∧ True :=
  ⟨calc11_set_2395_eq, calc11_set_2396_eq, calc11_set_2397_eq, calc11_set_2398_eq, calc11_set_2399_eq, calc11_set_2400_eq, calc11_set_2401_eq, calc11_set_2402_eq, calc11_set_2403_eq, calc11_set_2404_eq, calc11_set_2405_eq, calc11_set_2406_eq, calc11_set_2407_eq, calc11_set_2408_eq, calc11_set_2409_eq, calc11_set_2410_eq, True.intro⟩
