-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_Fix_R0
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:54:36.644147+00:00
-- url     : https://prove2.me/submissions/8f858353-f2b7-43e5-ba83-8e540ab33433

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA0
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndFix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution (n : ℕ) (hn0 : 0 ≤ n) (hn1 : n < 12500) :
    ((!Nat.blt (dimF (Nat.land (argF n) 65535)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.land (argF n) 65535)) (densSupG n))
        (densSupG (Nat.land (argF n) 65535))) = true) ∧
    ((!Nat.blt (dimF (Nat.shiftRight (argF n) 16)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.shiftRight (argF n) 16)) (densSupG n))
        (densSupG (Nat.shiftRight (argF n) 16))) = true) := by
  constructor
  · -- arg0
    by_cases h0 : n < 2500
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA0.land0_range n (by omega) h0
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA0.arg0] using h
    ·
      by_cases h1 : n < 5000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA1.land0_range n (by omega) h1
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA1.arg0] using h
      ·
        by_cases h2 : n < 7500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA2.land0_range n (by omega) h2
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA2.arg0] using h
        ·
          by_cases h3 : n < 10000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA3.land0_range n (by omega) h3
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA3.arg0] using h
          ·
            by_cases h4 : n < 12500
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA4.land0_range n (by omega) h4
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA4.arg0] using h
            ·
              omega
  · -- arg1
    by_cases h0 : n < 2500
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA0.land1_range n (by omega) h0
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA0.arg1] using h
    ·
      by_cases h1 : n < 5000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA1.land1_range n (by omega) h1
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA1.arg1] using h
      ·
        by_cases h2 : n < 7500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA2.land1_range n (by omega) h2
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA2.arg1] using h
        ·
          by_cases h3 : n < 10000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA3.land1_range n (by omega) h3
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA3.arg1] using h
          ·
            by_cases h4 : n < 12500
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA4.land1_range n (by omega) h4
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA4.arg1] using h
            ·
              omega
