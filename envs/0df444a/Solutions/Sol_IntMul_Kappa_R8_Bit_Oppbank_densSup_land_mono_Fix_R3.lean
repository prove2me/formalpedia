-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_Fix_R3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:54:38.740438+00:00
-- url     : https://prove2.me/submissions/e5838648-6dcf-4770-ba0f-b3a1b1d9884c

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA15
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA16
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA17
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA18
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA19
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndFix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution (n : ℕ) (hn0 : 37500 ≤ n) (hn1 : n < 50000) :
    ((!Nat.blt (dimF (Nat.land (argF n) 65535)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.land (argF n) 65535)) (densSupG n))
        (densSupG (Nat.land (argF n) 65535))) = true) ∧
    ((!Nat.blt (dimF (Nat.shiftRight (argF n) 16)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.shiftRight (argF n) 16)) (densSupG n))
        (densSupG (Nat.shiftRight (argF n) 16))) = true) := by
  constructor
  · -- arg0
    by_cases h15 : n < 40000
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA15.land0_range n (by omega) h15
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA15.arg0] using h
    ·
      by_cases h16 : n < 42500
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA16.land0_range n (by omega) h16
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA16.arg0] using h
      ·
        by_cases h17 : n < 45000
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA17.land0_range n (by omega) h17
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA17.arg0] using h
        ·
          by_cases h18 : n < 47500
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA18.land0_range n (by omega) h18
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA18.arg0] using h
          ·
            by_cases h19 : n < 50000
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA19.land0_range n (by omega) h19
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA19.arg0] using h
            ·
              omega
  · -- arg1
    by_cases h15 : n < 40000
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA15.land1_range n (by omega) h15
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA15.arg1] using h
    ·
      by_cases h16 : n < 42500
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA16.land1_range n (by omega) h16
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA16.arg1] using h
      ·
        by_cases h17 : n < 45000
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA17.land1_range n (by omega) h17
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA17.arg1] using h
        ·
          by_cases h18 : n < 47500
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA18.land1_range n (by omega) h18
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA18.arg1] using h
          ·
            by_cases h19 : n < 50000
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA19.land1_range n (by omega) h19
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA19.arg1] using h
            ·
              omega
