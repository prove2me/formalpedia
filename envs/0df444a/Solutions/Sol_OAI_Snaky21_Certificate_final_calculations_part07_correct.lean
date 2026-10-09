-- Prove2me | solution 1 for OAI.Snaky21.Certificate.final_calculations_part07_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:49:39.770675+00:00
-- url     : https://prove2.me/submissions/fe985d77-96cf-4754-8835-ad48d6be49af

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

theorem calc11_set_2411_eq : calc11_card_2314.envelope ∩ calc11_set_2410 = calc11_set_2411 := by decide +kernel
theorem calc11_set_2412_eq : calc11_card_2313.envelope ∩ calc11_set_2411 = calc11_set_2412 := by decide +kernel
theorem calc11_set_2413_eq : calc11_card_2312.envelope ∩ calc11_set_2412 = calc11_set_2413 := by decide +kernel
theorem calc11_set_2414_eq : calc11_card_2311.envelope ∩ calc11_set_2413 = calc11_set_2414 := by decide +kernel
theorem calc11_set_2415_eq : calc11_card_2310.envelope ∩ calc11_set_2414 = calc11_set_2415 := by decide +kernel
theorem calc11_set_2416_eq : calc11_card_2309.envelope ∩ calc11_set_2415 = calc11_set_2416 := by decide +kernel
theorem calc11_set_2417_eq : calc11_card_2308.envelope ∩ calc11_set_2416 = calc11_set_2417 := by decide +kernel
theorem calc11_set_2418_eq : calc11_card_2307.envelope ∩ calc11_set_2417 = calc11_set_2418 := by decide +kernel
theorem calc11_set_2419_eq : calc11_card_2306.envelope ∩ calc11_set_2418 = calc11_set_2419 := by decide +kernel
theorem calc11_set_2420_eq : calc11_card_2305.envelope ∩ calc11_set_2419 = calc11_set_2420 := by decide +kernel
theorem calc11_set_2421_eq : calc11_card_2304.envelope ∩ calc11_set_2420 = calc11_set_2421 := by decide +kernel
theorem calc11_set_2422_eq : calc11_card_2303.envelope ∩ calc11_set_2421 = calc11_set_2422 := by decide +kernel
theorem calc11_set_2423_eq : calc11_card_2302.envelope ∩ calc11_set_2422 = calc11_set_2423 := by decide +kernel
theorem calc11_set_2424_eq : calc11_card_2301.envelope ∩ calc11_set_2423 = calc11_set_2424 := by decide +kernel
theorem calc11_set_2425_eq : calc11_card_2300.envelope ∩ calc11_set_2424 = calc11_set_2425 := by decide +kernel
theorem calc11_set_2426_eq : calc11_set_2393 ∪ calc11_set_2425 = calc11_set_2426 := by decide +kernel
end OAI.Snaky21.Certificate

theorem solution : (calc11_card_2314.envelope ∩ calc11_set_2410 = calc11_set_2411) ∧ (calc11_card_2313.envelope ∩ calc11_set_2411 = calc11_set_2412) ∧ (calc11_card_2312.envelope ∩ calc11_set_2412 = calc11_set_2413) ∧ (calc11_card_2311.envelope ∩ calc11_set_2413 = calc11_set_2414) ∧ (calc11_card_2310.envelope ∩ calc11_set_2414 = calc11_set_2415) ∧ (calc11_card_2309.envelope ∩ calc11_set_2415 = calc11_set_2416) ∧ (calc11_card_2308.envelope ∩ calc11_set_2416 = calc11_set_2417) ∧ (calc11_card_2307.envelope ∩ calc11_set_2417 = calc11_set_2418) ∧ (calc11_card_2306.envelope ∩ calc11_set_2418 = calc11_set_2419) ∧ (calc11_card_2305.envelope ∩ calc11_set_2419 = calc11_set_2420) ∧ (calc11_card_2304.envelope ∩ calc11_set_2420 = calc11_set_2421) ∧ (calc11_card_2303.envelope ∩ calc11_set_2421 = calc11_set_2422) ∧ (calc11_card_2302.envelope ∩ calc11_set_2422 = calc11_set_2423) ∧ (calc11_card_2301.envelope ∩ calc11_set_2423 = calc11_set_2424) ∧ (calc11_card_2300.envelope ∩ calc11_set_2424 = calc11_set_2425) ∧ (calc11_set_2393 ∪ calc11_set_2425 = calc11_set_2426) ∧ True :=
  ⟨calc11_set_2411_eq, calc11_set_2412_eq, calc11_set_2413_eq, calc11_set_2414_eq, calc11_set_2415_eq, calc11_set_2416_eq, calc11_set_2417_eq, calc11_set_2418_eq, calc11_set_2419_eq, calc11_set_2420_eq, calc11_set_2421_eq, calc11_set_2422_eq, calc11_set_2423_eq, calc11_set_2424_eq, calc11_set_2425_eq, calc11_set_2426_eq, True.intro⟩
