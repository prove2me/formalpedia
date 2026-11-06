-- Prove2me | solution 2 for GraphProblems.cntN_le
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:15:19.334194+00:00
-- url     : https://prove2.me/submissions/ef983187-c00a-44f1-80c4-2afe1362e156

import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_WidthK_Top_Sat
import Mathlib.Tactic
import Definitions.Def_GraphProblems_Sized

set_option autoImplicit false

open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Finset

theorem solution (N : ℕ) (ψ : Fml) : cntN N ψ ≤ 2 ^ N := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp
