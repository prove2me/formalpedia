-- Prove2me | solution 1 for OAI.Snaky21.Certificate.final_calculations_part03_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:38:56.209452+00:00
-- url     : https://prove2.me/submissions/47400185-24bb-4e0e-93d8-6a205e4a6ddb

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

theorem calc11_set_2347_eq : calc11_card_2322.required ∪ calc11_set_2345 = calc11_set_2347 := by decide +kernel
theorem calc11_set_2348_eq : calc11_card_2322.envelope ∪ calc11_set_2346 = calc11_set_2348 := by decide +kernel
theorem calc11_set_2349_eq : calc11_card_2321.required ∪ calc11_set_2347 = calc11_set_2349 := by decide +kernel
theorem calc11_set_2350_eq : calc11_card_2321.envelope ∪ calc11_set_2348 = calc11_set_2350 := by decide +kernel
theorem calc11_set_2351_eq : calc11_card_2320.required ∪ calc11_set_2349 = calc11_set_2351 := by decide +kernel
theorem calc11_set_2352_eq : calc11_card_2320.envelope ∪ calc11_set_2350 = calc11_set_2352 := by decide +kernel
theorem calc11_set_2353_eq : calc11_card_2319.required ∪ calc11_set_2351 = calc11_set_2353 := by decide +kernel
theorem calc11_set_2354_eq : calc11_card_2319.envelope ∪ calc11_set_2352 = calc11_set_2354 := by decide +kernel
theorem calc11_set_2355_eq : calc11_card_2318.required ∪ calc11_set_2353 = calc11_set_2355 := by decide +kernel
theorem calc11_set_2356_eq : calc11_card_2318.envelope ∪ calc11_set_2354 = calc11_set_2356 := by decide +kernel
theorem calc11_set_2357_eq : calc11_card_2317.required ∪ calc11_set_2355 = calc11_set_2357 := by decide +kernel
theorem calc11_set_2358_eq : calc11_card_2317.envelope ∪ calc11_set_2356 = calc11_set_2358 := by decide +kernel
theorem calc11_set_2359_eq : calc11_card_2316.required ∪ calc11_set_2357 = calc11_set_2359 := by decide +kernel
theorem calc11_set_2360_eq : calc11_card_2316.envelope ∪ calc11_set_2358 = calc11_set_2360 := by decide +kernel
theorem calc11_set_2361_eq : calc11_card_2315.required ∪ calc11_set_2359 = calc11_set_2361 := by decide +kernel
theorem calc11_set_2362_eq : calc11_card_2315.envelope ∪ calc11_set_2360 = calc11_set_2362 := by decide +kernel
end OAI.Snaky21.Certificate

theorem solution : (calc11_card_2322.required ∪ calc11_set_2345 = calc11_set_2347) ∧ (calc11_card_2322.envelope ∪ calc11_set_2346 = calc11_set_2348) ∧ (calc11_card_2321.required ∪ calc11_set_2347 = calc11_set_2349) ∧ (calc11_card_2321.envelope ∪ calc11_set_2348 = calc11_set_2350) ∧ (calc11_card_2320.required ∪ calc11_set_2349 = calc11_set_2351) ∧ (calc11_card_2320.envelope ∪ calc11_set_2350 = calc11_set_2352) ∧ (calc11_card_2319.required ∪ calc11_set_2351 = calc11_set_2353) ∧ (calc11_card_2319.envelope ∪ calc11_set_2352 = calc11_set_2354) ∧ (calc11_card_2318.required ∪ calc11_set_2353 = calc11_set_2355) ∧ (calc11_card_2318.envelope ∪ calc11_set_2354 = calc11_set_2356) ∧ (calc11_card_2317.required ∪ calc11_set_2355 = calc11_set_2357) ∧ (calc11_card_2317.envelope ∪ calc11_set_2356 = calc11_set_2358) ∧ (calc11_card_2316.required ∪ calc11_set_2357 = calc11_set_2359) ∧ (calc11_card_2316.envelope ∪ calc11_set_2358 = calc11_set_2360) ∧ (calc11_card_2315.required ∪ calc11_set_2359 = calc11_set_2361) ∧ (calc11_card_2315.envelope ∪ calc11_set_2360 = calc11_set_2362) ∧ True :=
  ⟨calc11_set_2347_eq, calc11_set_2348_eq, calc11_set_2349_eq, calc11_set_2350_eq, calc11_set_2351_eq, calc11_set_2352_eq, calc11_set_2353_eq, calc11_set_2354_eq, calc11_set_2355_eq, calc11_set_2356_eq, calc11_set_2357_eq, calc11_set_2358_eq, calc11_set_2359_eq, calc11_set_2360_eq, calc11_set_2361_eq, calc11_set_2362_eq, True.intro⟩
