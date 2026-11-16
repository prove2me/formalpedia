-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.argRel_dim_le_R1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:47:48.599111+00:00
-- url     : https://prove2.me/submissions/0d9aa3c5-ecfb-4e18-8c83-1d9b8f29e2be

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA5
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA6
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA7
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA8
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA9
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
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 15000
  · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA5.dim0_range n (by omega) h0, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA5.dim1_range n (by omega) h0⟩
  · by_cases h1 : n < 17500
    · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA6.dim0_range n (by omega) h1, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA6.dim1_range n (by omega) h1⟩
    · by_cases h2 : n < 20000
      · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA7.dim0_range n (by omega) h2, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA7.dim1_range n (by omega) h2⟩
      · by_cases h3 : n < 22500
        · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA8.dim0_range n (by omega) h3, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA8.dim1_range n (by omega) h3⟩
        · exact ⟨IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA9.dim0_range n (by omega) hn1, IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA9.dim1_range n (by omega) hn1⟩
