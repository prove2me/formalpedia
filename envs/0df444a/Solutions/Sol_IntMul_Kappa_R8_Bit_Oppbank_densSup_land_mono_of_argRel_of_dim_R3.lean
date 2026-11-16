-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_of_argRel_of_dim_R3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:11:43.765257+00:00
-- url     : https://prove2.me/submissions/38868890-15fd-4775-a3b7-e49f990ff895

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA15
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA16
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA17
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA18
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA19
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
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
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA15.land0_range n (by omega) h15
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA15.arg0] using h
    ·
      by_cases h16 : n < 42500
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA16.land0_range n (by omega) h16
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA16.arg0] using h
      ·
        by_cases h17 : n < 45000
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA17.land0_range n (by omega) h17
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA17.arg0] using h
        ·
          by_cases h18 : n < 47500
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA18.land0_range n (by omega) h18
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA18.arg0] using h
          ·
            by_cases h19 : n < 50000
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA19.land0_range n (by omega) h19
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA19.arg0] using h
            ·
              omega
  · -- arg1
    by_cases h15 : n < 40000
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA15.land1_range n (by omega) h15
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA15.arg1] using h
    ·
      by_cases h16 : n < 42500
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA16.land1_range n (by omega) h16
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA16.arg1] using h
      ·
        by_cases h17 : n < 45000
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA17.land1_range n (by omega) h17
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA17.arg1] using h
        ·
          by_cases h18 : n < 47500
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA18.land1_range n (by omega) h18
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA18.arg1] using h
          ·
            by_cases h19 : n < 50000
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA19.land1_range n (by omega) h19
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA19.arg1] using h
            ·
              omega
