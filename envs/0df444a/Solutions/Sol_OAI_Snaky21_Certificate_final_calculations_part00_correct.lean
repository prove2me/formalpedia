-- Prove2me | solution 1 for OAI.Snaky21.Certificate.final_calculations_part00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:34:01.372238+00:00
-- url     : https://prove2.me/submissions/c1b5adeb-7dc0-4a97-bf92-1f42d8f30375

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

theorem calc11_card_2299_eq : placed 0 (4, 3) card_648 = calc11_card_2299 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2300_eq : placed 1 (3, 4) card_648 = calc11_card_2300 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2301_eq : placed 5 (3, 12) card_648 = calc11_card_2301 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2302_eq : placed 2 (4, 13) card_648 = calc11_card_2302 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2303_eq : placed 1 (0, 0) card_708 = calc11_card_2303 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2304_eq : placed 4 (16, 0) card_708 = calc11_card_2304 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2305_eq : placed 2 (0, 16) card_708 = calc11_card_2305 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2306_eq : placed 7 (16, 16) card_708 = calc11_card_2306 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2307_eq : placed 0 (3, 3) card_712 = calc11_card_2307 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2308_eq : placed 1 (3, 3) card_712 = calc11_card_2308 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2309_eq : placed 4 (13, 3) card_712 = calc11_card_2309 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2310_eq : placed 5 (3, 13) card_712 = calc11_card_2310 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2311_eq : placed 2 (3, 13) card_712 = calc11_card_2311 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2312_eq : placed 3 (13, 3) card_712 = calc11_card_2312 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2313_eq : placed 6 (13, 13) card_712 = calc11_card_2313 := by
  apply computed_card_ext <;> decide +kernel
theorem calc11_card_2314_eq : placed 7 (13, 13) card_712 = calc11_card_2314 := by
  apply computed_card_ext <;> decide +kernel
end OAI.Snaky21.Certificate

theorem solution : (placed 0 (4, 3) card_648 = calc11_card_2299) ∧ (placed 1 (3, 4) card_648 = calc11_card_2300) ∧ (placed 5 (3, 12) card_648 = calc11_card_2301) ∧ (placed 2 (4, 13) card_648 = calc11_card_2302) ∧ (placed 1 (0, 0) card_708 = calc11_card_2303) ∧ (placed 4 (16, 0) card_708 = calc11_card_2304) ∧ (placed 2 (0, 16) card_708 = calc11_card_2305) ∧ (placed 7 (16, 16) card_708 = calc11_card_2306) ∧ (placed 0 (3, 3) card_712 = calc11_card_2307) ∧ (placed 1 (3, 3) card_712 = calc11_card_2308) ∧ (placed 4 (13, 3) card_712 = calc11_card_2309) ∧ (placed 5 (3, 13) card_712 = calc11_card_2310) ∧ (placed 2 (3, 13) card_712 = calc11_card_2311) ∧ (placed 3 (13, 3) card_712 = calc11_card_2312) ∧ (placed 6 (13, 13) card_712 = calc11_card_2313) ∧ (placed 7 (13, 13) card_712 = calc11_card_2314) ∧ True :=
  ⟨calc11_card_2299_eq, calc11_card_2300_eq, calc11_card_2301_eq, calc11_card_2302_eq, calc11_card_2303_eq, calc11_card_2304_eq, calc11_card_2305_eq, calc11_card_2306_eq, calc11_card_2307_eq, calc11_card_2308_eq, calc11_card_2309_eq, calc11_card_2310_eq, calc11_card_2311_eq, calc11_card_2312_eq, calc11_card_2313_eq, calc11_card_2314_eq, True.intro⟩
