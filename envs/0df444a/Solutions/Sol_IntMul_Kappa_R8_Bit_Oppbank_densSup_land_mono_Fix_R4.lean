-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_Fix_R4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:54:39.813117+00:00
-- url     : https://prove2.me/submissions/ead605c6-7505-4457-8dde-500213134e4e

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA20
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA21
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA22
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA23
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA24
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndFix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution (n : ℕ) (hn0 : 50000 ≤ n) (hn1 : n < 62478) :
    ((!Nat.blt (dimF (Nat.land (argF n) 65535)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.land (argF n) 65535)) (densSupG n))
        (densSupG (Nat.land (argF n) 65535))) = true) ∧
    ((!Nat.blt (dimF (Nat.shiftRight (argF n) 16)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.shiftRight (argF n) 16)) (densSupG n))
        (densSupG (Nat.shiftRight (argF n) 16))) = true) := by
  constructor
  · -- arg0
    by_cases h20 : n < 52500
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA20.land0_range n (by omega) h20
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA20.arg0] using h
    ·
      by_cases h21 : n < 55000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA21.land0_range n (by omega) h21
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA21.arg0] using h
      ·
        by_cases h22 : n < 57500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA22.land0_range n (by omega) h22
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA22.arg0] using h
        ·
          by_cases h23 : n < 60000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA23.land0_range n (by omega) h23
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA23.arg0] using h
          ·
            by_cases h24 : n < 62478
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA24.land0_range n (by omega) h24
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA24.arg0] using h
            ·
              omega
  · -- arg1
    by_cases h20 : n < 52500
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA20.land1_range n (by omega) h20
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA20.arg1] using h
    ·
      by_cases h21 : n < 55000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA21.land1_range n (by omega) h21
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA21.arg1] using h
      ·
        by_cases h22 : n < 57500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA22.land1_range n (by omega) h22
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA22.arg1] using h
        ·
          by_cases h23 : n < 60000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA23.land1_range n (by omega) h23
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA23.arg1] using h
          ·
            by_cases h24 : n < 62478
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA24.land1_range n (by omega) h24
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA24.arg1] using h
            ·
              omega
