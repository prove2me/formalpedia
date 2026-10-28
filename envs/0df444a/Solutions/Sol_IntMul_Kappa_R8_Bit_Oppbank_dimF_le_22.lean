-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.dimF_le_22
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:34:15.280917+00:00
-- url     : https://prove2.me/submissions/d7fea56e-f71b-41c0-b0d2-2241920d9a20

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.DimBound

theorem solution : ∀ n < SupG.nNodes, dimF n ≤ 22 :=
  DimBound.dimF_le_22
