-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_AllOneRun
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:14:31.314436+00:00
-- url     : https://prove2.me/submissions/cd542fa9-3751-4e49-95dc-54698e93903d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMomExpand
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_edges_oneRun
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank.OneRunMomExpand
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution : AllOneRun := by
  intro e he
  exact Or.inr (net0O2_edges_oneRun e he)
