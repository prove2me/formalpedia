-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_of_argRel_of_dim_R0
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:11:42.104136+00:00
-- url     : https://prove2.me/submissions/240a69c4-4525-4b23-9e46-662bc8f0836f

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA0
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoA4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
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
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA0.land0_range n (by omega) h0
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA0.arg0] using h
    ·
      by_cases h1 : n < 5000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA1.land0_range n (by omega) h1
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA1.arg0] using h
      ·
        by_cases h2 : n < 7500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA2.land0_range n (by omega) h2
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA2.arg0] using h
        ·
          by_cases h3 : n < 10000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA3.land0_range n (by omega) h3
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA3.arg0] using h
          ·
            by_cases h4 : n < 12500
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA4.land0_range n (by omega) h4
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA4.arg0] using h
            ·
              omega
  · -- arg1
    by_cases h0 : n < 2500
    ·
      have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA0.land1_range n (by omega) h0
      simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA0.arg1] using h
    ·
      by_cases h1 : n < 5000
      ·
        have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA1.land1_range n (by omega) h1
        simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA1.arg1] using h
      ·
        by_cases h2 : n < 7500
        ·
          have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA2.land1_range n (by omega) h2
          simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA2.arg1] using h
        ·
          by_cases h3 : n < 10000
          ·
            have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA3.land1_range n (by omega) h3
            simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA3.arg1] using h
          ·
            by_cases h4 : n < 12500
            ·
              have h := IntMul.Kappa.R8.Bit.Oppbank.LandMonoA4.land1_range n (by omega) h4
              simpa [IntMul.Kappa.R8.Bit.Oppbank.LandMonoA4.arg1] using h
            ·
              omega
