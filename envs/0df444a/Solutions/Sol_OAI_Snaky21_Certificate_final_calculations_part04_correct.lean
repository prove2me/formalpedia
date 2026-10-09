-- Prove2me | solution 1 for OAI.Snaky21.Certificate.final_calculations_part04_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:42:46.390979+00:00
-- url     : https://prove2.me/submissions/71e44cf5-0c47-4478-a88c-95efc64931a3

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

theorem calc11_set_2363_eq : calc11_card_2314.required ∪ calc11_set_2361 = calc11_set_2363 := by decide +kernel
theorem calc11_set_2364_eq : calc11_card_2314.envelope ∪ calc11_set_2362 = calc11_set_2364 := by decide +kernel
theorem calc11_set_2365_eq : calc11_card_2313.required ∪ calc11_set_2363 = calc11_set_2365 := by decide +kernel
theorem calc11_set_2366_eq : calc11_card_2313.envelope ∪ calc11_set_2364 = calc11_set_2366 := by decide +kernel
theorem calc11_set_2367_eq : calc11_card_2312.required ∪ calc11_set_2365 = calc11_set_2367 := by decide +kernel
theorem calc11_set_2368_eq : calc11_card_2312.envelope ∪ calc11_set_2366 = calc11_set_2368 := by decide +kernel
theorem calc11_set_2369_eq : calc11_card_2311.required ∪ calc11_set_2367 = calc11_set_2369 := by decide +kernel
theorem calc11_set_2370_eq : calc11_card_2311.envelope ∪ calc11_set_2368 = calc11_set_2370 := by decide +kernel
theorem calc11_set_2371_eq : calc11_card_2310.required ∪ calc11_set_2369 = calc11_set_2371 := by decide +kernel
theorem calc11_set_2372_eq : calc11_card_2310.envelope ∪ calc11_set_2370 = calc11_set_2372 := by decide +kernel
theorem calc11_set_2373_eq : calc11_card_2309.required ∪ calc11_set_2371 = calc11_set_2373 := by decide +kernel
theorem calc11_set_2374_eq : calc11_card_2309.envelope ∪ calc11_set_2372 = calc11_set_2374 := by decide +kernel
theorem calc11_set_2375_eq : calc11_card_2308.required ∪ calc11_set_2373 = calc11_set_2375 := by decide +kernel
theorem calc11_set_2376_eq : calc11_card_2308.envelope ∪ calc11_set_2374 = calc11_set_2376 := by decide +kernel
theorem calc11_set_2377_eq : calc11_card_2307.required ∪ calc11_set_2375 = calc11_set_2377 := by decide +kernel
theorem calc11_set_2378_eq : calc11_card_2307.envelope ∪ calc11_set_2376 = calc11_set_2378 := by decide +kernel
end OAI.Snaky21.Certificate

theorem solution : (calc11_card_2314.required ∪ calc11_set_2361 = calc11_set_2363) ∧ (calc11_card_2314.envelope ∪ calc11_set_2362 = calc11_set_2364) ∧ (calc11_card_2313.required ∪ calc11_set_2363 = calc11_set_2365) ∧ (calc11_card_2313.envelope ∪ calc11_set_2364 = calc11_set_2366) ∧ (calc11_card_2312.required ∪ calc11_set_2365 = calc11_set_2367) ∧ (calc11_card_2312.envelope ∪ calc11_set_2366 = calc11_set_2368) ∧ (calc11_card_2311.required ∪ calc11_set_2367 = calc11_set_2369) ∧ (calc11_card_2311.envelope ∪ calc11_set_2368 = calc11_set_2370) ∧ (calc11_card_2310.required ∪ calc11_set_2369 = calc11_set_2371) ∧ (calc11_card_2310.envelope ∪ calc11_set_2370 = calc11_set_2372) ∧ (calc11_card_2309.required ∪ calc11_set_2371 = calc11_set_2373) ∧ (calc11_card_2309.envelope ∪ calc11_set_2372 = calc11_set_2374) ∧ (calc11_card_2308.required ∪ calc11_set_2373 = calc11_set_2375) ∧ (calc11_card_2308.envelope ∪ calc11_set_2374 = calc11_set_2376) ∧ (calc11_card_2307.required ∪ calc11_set_2375 = calc11_set_2377) ∧ (calc11_card_2307.envelope ∪ calc11_set_2376 = calc11_set_2378) ∧ True :=
  ⟨calc11_set_2363_eq, calc11_set_2364_eq, calc11_set_2365_eq, calc11_set_2366_eq, calc11_set_2367_eq, calc11_set_2368_eq, calc11_set_2369_eq, calc11_set_2370_eq, calc11_set_2371_eq, calc11_set_2372_eq, calc11_set_2373_eq, calc11_set_2374_eq, calc11_set_2375_eq, calc11_set_2376_eq, calc11_set_2377_eq, calc11_set_2378_eq, True.intro⟩
