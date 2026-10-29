-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_Fix_R2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:54:38.047997+00:00
-- url     : https://prove2.me/submissions/71a03388-5166-4ec3-8365-499d471480d0

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA10
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA11
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA12
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA13
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA14
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndFix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution (n : ℕ) (hn0 : 25000 ≤ n) (hn1 : n < 37500) :
    ((!Nat.blt (dimF (Nat.land (argF n) 65535)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.land (argF n) 65535)) (densSupG n))
        (densSupG (Nat.land (argF n) 65535))) = true) ∧
    ((!Nat.blt (dimF (Nat.shiftRight (argF n) 16)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.shiftRight (argF n) 16)) (densSupG n))
        (densSupG (Nat.shiftRight (argF n) 16))) = true) := by
  constructor
  · -- arg0
    by_cases h10 : n < 27500
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA10.land0_range n (by omega) h10
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA10.arg0] using h
    ·
      by_cases h11 : n < 30000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA11.land0_range n (by omega) h11
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA11.arg0] using h
      ·
        by_cases h12 : n < 32500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA12.land0_range n (by omega) h12
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA12.arg0] using h
        ·
          by_cases h13 : n < 35000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA13.land0_range n (by omega) h13
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA13.arg0] using h
          ·
            by_cases h14 : n < 37500
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA14.land0_range n (by omega) h14
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA14.arg0] using h
            ·
              omega
  · -- arg1
    by_cases h10 : n < 27500
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA10.land1_range n (by omega) h10
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA10.arg1] using h
    ·
      by_cases h11 : n < 30000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA11.land1_range n (by omega) h11
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA11.arg1] using h
      ·
        by_cases h12 : n < 32500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA12.land1_range n (by omega) h12
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA12.arg1] using h
        ·
          by_cases h13 : n < 35000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA13.land1_range n (by omega) h13
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA13.arg1] using h
          ·
            by_cases h14 : n < 37500
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA14.land1_range n (by omega) h14
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA14.arg1] using h
            ·
              omega
