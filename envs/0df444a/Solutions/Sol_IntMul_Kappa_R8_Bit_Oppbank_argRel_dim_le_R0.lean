-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.argRel_dim_le_R0
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:47:48.11871+00:00
-- url     : https://prove2.me/submissions/a1004cd5-9753-4387-b345-29f6b0826f5b

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA0
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA4
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
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 2500
  · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA0.dim0_range n (by omega) h0, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA0.dim1_range n (by omega) h0⟩
  · by_cases h1 : n < 5000
    · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA1.dim0_range n (by omega) h1, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA1.dim1_range n (by omega) h1⟩
    · by_cases h2 : n < 7500
      · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA2.dim0_range n (by omega) h2, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA2.dim1_range n (by omega) h2⟩
      · by_cases h3 : n < 10000
        · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA3.dim0_range n (by omega) h3, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA3.dim1_range n (by omega) h3⟩
        · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA4.dim0_range n (by omega) hn1, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA4.dim1_range n (by omega) hn1⟩
