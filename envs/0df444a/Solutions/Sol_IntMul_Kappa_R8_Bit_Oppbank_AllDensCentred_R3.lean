-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:31:39.603308+00:00
-- url     : https://prove2.me/submissions/64f036a8-171d-4efe-a328-812c646c0276

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R3a
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R3b
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution :
    ∀ n, 45000 ≤ n → n < 62478 → HasCentre (densSupG n) := by
  intro n h1 h2
  by_cases h : n < 55000
  · exact IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R3a n h1 h
  · exact IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R3b n (by omega) h2
