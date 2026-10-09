-- Prove2me | solution 1 for OAI.Snaky21.Certificate.final_calculations_part02_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:38:31.233981+00:00
-- url     : https://prove2.me/submissions/d32ebd2c-5b40-4035-81f8-65cde9dee25d

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

theorem calc11_set_2331_eq : calc11_card_2330.required ∪ ∅ = calc11_set_2331 := by decide +kernel
theorem calc11_set_2332_eq : calc11_card_2330.envelope ∪ ∅ = calc11_set_2332 := by decide +kernel
theorem calc11_set_2333_eq : calc11_card_2329.required ∪ calc11_set_2331 = calc11_set_2333 := by decide +kernel
theorem calc11_set_2334_eq : calc11_card_2329.envelope ∪ calc11_set_2332 = calc11_set_2334 := by decide +kernel
theorem calc11_set_2335_eq : calc11_card_2328.required ∪ calc11_set_2333 = calc11_set_2335 := by decide +kernel
theorem calc11_set_2336_eq : calc11_card_2328.envelope ∪ calc11_set_2334 = calc11_set_2336 := by decide +kernel
theorem calc11_set_2337_eq : calc11_card_2327.required ∪ calc11_set_2335 = calc11_set_2337 := by decide +kernel
theorem calc11_set_2338_eq : calc11_card_2327.envelope ∪ calc11_set_2336 = calc11_set_2338 := by decide +kernel
theorem calc11_set_2339_eq : calc11_card_2326.required ∪ calc11_set_2337 = calc11_set_2339 := by decide +kernel
theorem calc11_set_2340_eq : calc11_card_2326.envelope ∪ calc11_set_2338 = calc11_set_2340 := by decide +kernel
theorem calc11_set_2341_eq : calc11_card_2325.required ∪ calc11_set_2339 = calc11_set_2341 := by decide +kernel
theorem calc11_set_2342_eq : calc11_card_2325.envelope ∪ calc11_set_2340 = calc11_set_2342 := by decide +kernel
theorem calc11_set_2343_eq : calc11_card_2324.required ∪ calc11_set_2341 = calc11_set_2343 := by decide +kernel
theorem calc11_set_2344_eq : calc11_card_2324.envelope ∪ calc11_set_2342 = calc11_set_2344 := by decide +kernel
theorem calc11_set_2345_eq : calc11_card_2323.required ∪ calc11_set_2343 = calc11_set_2345 := by decide +kernel
theorem calc11_set_2346_eq : calc11_card_2323.envelope ∪ calc11_set_2344 = calc11_set_2346 := by decide +kernel
end OAI.Snaky21.Certificate

theorem solution : (calc11_card_2330.required ∪ ∅ = calc11_set_2331) ∧ (calc11_card_2330.envelope ∪ ∅ = calc11_set_2332) ∧ (calc11_card_2329.required ∪ calc11_set_2331 = calc11_set_2333) ∧ (calc11_card_2329.envelope ∪ calc11_set_2332 = calc11_set_2334) ∧ (calc11_card_2328.required ∪ calc11_set_2333 = calc11_set_2335) ∧ (calc11_card_2328.envelope ∪ calc11_set_2334 = calc11_set_2336) ∧ (calc11_card_2327.required ∪ calc11_set_2335 = calc11_set_2337) ∧ (calc11_card_2327.envelope ∪ calc11_set_2336 = calc11_set_2338) ∧ (calc11_card_2326.required ∪ calc11_set_2337 = calc11_set_2339) ∧ (calc11_card_2326.envelope ∪ calc11_set_2338 = calc11_set_2340) ∧ (calc11_card_2325.required ∪ calc11_set_2339 = calc11_set_2341) ∧ (calc11_card_2325.envelope ∪ calc11_set_2340 = calc11_set_2342) ∧ (calc11_card_2324.required ∪ calc11_set_2341 = calc11_set_2343) ∧ (calc11_card_2324.envelope ∪ calc11_set_2342 = calc11_set_2344) ∧ (calc11_card_2323.required ∪ calc11_set_2343 = calc11_set_2345) ∧ (calc11_card_2323.envelope ∪ calc11_set_2344 = calc11_set_2346) ∧ True :=
  ⟨calc11_set_2331_eq, calc11_set_2332_eq, calc11_set_2333_eq, calc11_set_2334_eq, calc11_set_2335_eq, calc11_set_2336_eq, calc11_set_2337_eq, calc11_set_2338_eq, calc11_set_2339_eq, calc11_set_2340_eq, calc11_set_2341_eq, calc11_set_2342_eq, calc11_set_2343_eq, calc11_set_2344_eq, calc11_set_2345_eq, calc11_set_2346_eq, True.intro⟩
