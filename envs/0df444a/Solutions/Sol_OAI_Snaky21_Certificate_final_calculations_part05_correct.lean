-- Prove2me | solution 1 for OAI.Snaky21.Certificate.final_calculations_part05_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:48:18.447969+00:00
-- url     : https://prove2.me/submissions/df77b0de-10bc-4e3c-b90b-24fcf8e5b42d

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

theorem calc11_set_2379_eq : calc11_card_2306.required ∪ calc11_set_2377 = calc11_set_2379 := by decide +kernel
theorem calc11_set_2380_eq : calc11_card_2306.envelope ∪ calc11_set_2378 = calc11_set_2380 := by decide +kernel
theorem calc11_set_2381_eq : calc11_card_2305.required ∪ calc11_set_2379 = calc11_set_2381 := by decide +kernel
theorem calc11_set_2382_eq : calc11_card_2305.envelope ∪ calc11_set_2380 = calc11_set_2382 := by decide +kernel
theorem calc11_set_2383_eq : calc11_card_2304.required ∪ calc11_set_2381 = calc11_set_2383 := by decide +kernel
theorem calc11_set_2384_eq : calc11_card_2304.envelope ∪ calc11_set_2382 = calc11_set_2384 := by decide +kernel
theorem calc11_set_2385_eq : calc11_card_2303.required ∪ calc11_set_2383 = calc11_set_2385 := by decide +kernel
theorem calc11_set_2386_eq : calc11_card_2303.envelope ∪ calc11_set_2384 = calc11_set_2386 := by decide +kernel
theorem calc11_set_2387_eq : calc11_card_2302.required ∪ calc11_set_2385 = calc11_set_2387 := by decide +kernel
theorem calc11_set_2388_eq : calc11_card_2302.envelope ∪ calc11_set_2386 = calc11_set_2388 := by decide +kernel
theorem calc11_set_2389_eq : calc11_card_2301.required ∪ calc11_set_2387 = calc11_set_2389 := by decide +kernel
theorem calc11_set_2390_eq : calc11_card_2301.envelope ∪ calc11_set_2388 = calc11_set_2390 := by decide +kernel
theorem calc11_set_2391_eq : calc11_card_2300.required ∪ calc11_set_2389 = calc11_set_2391 := by decide +kernel
theorem calc11_set_2392_eq : calc11_card_2300.envelope ∪ calc11_set_2390 = calc11_set_2392 := by decide +kernel
theorem calc11_set_2393_eq : calc11_card_2299.required ∪ calc11_set_2391 = calc11_set_2393 := by decide +kernel
theorem calc11_set_2394_eq : calc11_card_2299.envelope ∪ calc11_set_2392 = calc11_set_2394 := by decide +kernel
end OAI.Snaky21.Certificate

theorem solution : (calc11_card_2306.required ∪ calc11_set_2377 = calc11_set_2379) ∧ (calc11_card_2306.envelope ∪ calc11_set_2378 = calc11_set_2380) ∧ (calc11_card_2305.required ∪ calc11_set_2379 = calc11_set_2381) ∧ (calc11_card_2305.envelope ∪ calc11_set_2380 = calc11_set_2382) ∧ (calc11_card_2304.required ∪ calc11_set_2381 = calc11_set_2383) ∧ (calc11_card_2304.envelope ∪ calc11_set_2382 = calc11_set_2384) ∧ (calc11_card_2303.required ∪ calc11_set_2383 = calc11_set_2385) ∧ (calc11_card_2303.envelope ∪ calc11_set_2384 = calc11_set_2386) ∧ (calc11_card_2302.required ∪ calc11_set_2385 = calc11_set_2387) ∧ (calc11_card_2302.envelope ∪ calc11_set_2386 = calc11_set_2388) ∧ (calc11_card_2301.required ∪ calc11_set_2387 = calc11_set_2389) ∧ (calc11_card_2301.envelope ∪ calc11_set_2388 = calc11_set_2390) ∧ (calc11_card_2300.required ∪ calc11_set_2389 = calc11_set_2391) ∧ (calc11_card_2300.envelope ∪ calc11_set_2390 = calc11_set_2392) ∧ (calc11_card_2299.required ∪ calc11_set_2391 = calc11_set_2393) ∧ (calc11_card_2299.envelope ∪ calc11_set_2392 = calc11_set_2394) ∧ True :=
  ⟨calc11_set_2379_eq, calc11_set_2380_eq, calc11_set_2381_eq, calc11_set_2382_eq, calc11_set_2383_eq, calc11_set_2384_eq, calc11_set_2385_eq, calc11_set_2386_eq, calc11_set_2387_eq, calc11_set_2388_eq, calc11_set_2389_eq, calc11_set_2390_eq, calc11_set_2391_eq, calc11_set_2392_eq, calc11_set_2393_eq, calc11_set_2394_eq, True.intro⟩
