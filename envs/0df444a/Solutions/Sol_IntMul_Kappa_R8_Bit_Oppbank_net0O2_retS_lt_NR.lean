-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_retS_lt_NR
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:22:02.918197+00:00
-- url     : https://prove2.me/submissions/ca8adf42-18bb-4e1a-98c7-23c7c5da2f10

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NR h)

private theorem retS_eq : ∀ c < 23, retS c = #[140, 143, 2855, 2858, 5082, 5085, 6869, 6872, 8264, 8267, 9315, 9318, 10070, 10073, 10577, 10580, 10884, 10887, 11039, 11042, 11090, 11093, 11096][c]! := by
  intro c hc
  interval_cases c
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- Platform sol name for `net0O2_retS_lt_NR`. -/
theorem solution (c : ℕ) (hc : c < h) : retS c < NR := by
  have hc' : c < 23 := by simpa [h] using hc
  have hEq := retS_eq c hc'
  have hlt : #[140, 143, 2855, 2858, 5082, 5085, 6869, 6872, 8264, 8267, 9315, 9318, 10070, 10073, 10577, 10580, 10884, 10887, 11039, 11042, 11090, 11093, 11096][c]! < NR := by
    simp only [NR]
    interval_cases c <;> decide
  simpa [hEq] using hlt
