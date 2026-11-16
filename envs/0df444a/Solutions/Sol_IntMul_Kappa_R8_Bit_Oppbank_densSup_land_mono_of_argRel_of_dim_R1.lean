-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_of_argRel_of_dim_R1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:11:42.584648+00:00
-- url     : https://prove2.me/submissions/f64d8dc6-b25b-4245-beb0-11d8f7b63029

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA5
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA6
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA7
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA8
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA9
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution (n : ℕ) (hn0 : 12500 ≤ n) (hn1 : n < 25000) :
    ((!Nat.blt (dimF (Nat.land (argF n) 65535)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.land (argF n) 65535)) (densSupG n))
        (densSupG (Nat.land (argF n) 65535))) = true) ∧
    ((!Nat.blt (dimF (Nat.shiftRight (argF n) 16)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.shiftRight (argF n) 16)) (densSupG n))
        (densSupG (Nat.shiftRight (argF n) 16))) = true) := by
  constructor
  · -- arg0
    by_cases h5 : n < 15000
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA5.land0_range n (by omega) h5
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA5.arg0] using h
    ·
      by_cases h6 : n < 17500
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA6.land0_range n (by omega) h6
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA6.arg0] using h
      ·
        by_cases h7 : n < 20000
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA7.land0_range n (by omega) h7
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA7.arg0] using h
        ·
          by_cases h8 : n < 22500
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA8.land0_range n (by omega) h8
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA8.arg0] using h
          ·
            by_cases h9 : n < 25000
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA9.land0_range n (by omega) h9
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA9.arg0] using h
            ·
              omega
  · -- arg1
    by_cases h5 : n < 15000
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA5.land1_range n (by omega) h5
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA5.arg1] using h
    ·
      by_cases h6 : n < 17500
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA6.land1_range n (by omega) h6
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA6.arg1] using h
      ·
        by_cases h7 : n < 20000
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA7.land1_range n (by omega) h7
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA7.arg1] using h
        ·
          by_cases h8 : n < 22500
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA8.land1_range n (by omega) h8
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA8.arg1] using h
          ·
            by_cases h9 : n < 25000
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA9.land1_range n (by omega) h9
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA9.arg1] using h
            ·
              omega
