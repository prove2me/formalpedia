-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_of_argRel_of_dim_R4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:11:44.30519+00:00
-- url     : https://prove2.me/submissions/a72b9bdb-6302-458d-917f-327688f19912

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA20
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA21
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA22
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA23
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA24
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
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
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA20.land0_range n (by omega) h20
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA20.arg0] using h
    ·
      by_cases h21 : n < 55000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA21.land0_range n (by omega) h21
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA21.arg0] using h
      ·
        by_cases h22 : n < 57500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA22.land0_range n (by omega) h22
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA22.arg0] using h
        ·
          by_cases h23 : n < 60000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA23.land0_range n (by omega) h23
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA23.arg0] using h
          ·
            by_cases h24 : n < 62478
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA24.land0_range n (by omega) h24
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA24.arg0] using h
            ·
              omega
  · -- arg1
    by_cases h20 : n < 52500
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA20.land1_range n (by omega) h20
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA20.arg1] using h
    ·
      by_cases h21 : n < 55000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA21.land1_range n (by omega) h21
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA21.arg1] using h
      ·
        by_cases h22 : n < 57500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA22.land1_range n (by omega) h22
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA22.arg1] using h
        ·
          by_cases h23 : n < 60000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA23.land1_range n (by omega) h23
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA23.arg1] using h
          ·
            by_cases h24 : n < 62478
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA24.land1_range n (by omega) h24
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA24.arg1] using h
            ·
              omega
