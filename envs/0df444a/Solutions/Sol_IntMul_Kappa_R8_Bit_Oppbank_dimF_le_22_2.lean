-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.dimF_le_22
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:43:31.925414+00:00
-- url     : https://prove2.me/submissions/f3ccae23-bdfb-449d-ab5f-f4a8596f0481

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.DimBound

/-- Densified `dimF ≤ 22` for every node (DimBound combiner). -/
theorem solution : ∀ n < IntMul.Kappa.R8.Bit.Oppbank.SupG.nNodes, dimF n ≤ 22 :=
  dimF_le_22
