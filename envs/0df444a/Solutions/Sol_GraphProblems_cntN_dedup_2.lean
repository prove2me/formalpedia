-- Prove2me | solution 2 for GraphProblems.cntN_dedup
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:15:19.862335+00:00
-- url     : https://prove2.me/submissions/a814ab29-cb1a-45f8-9d61-f108ceaa4577

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
import Theorems.Thm_Groundwork_PolyT_dedup
attribute [local fun_prop] Groundwork.PolyT.dedup

set_option autoImplicit false

open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Finset

theorem solution (N : ℕ) (ψ : Fml) : cntN N ψ.dedup = cntN N ψ := by
  unfold cntN
  exact congrArg Finset.card (Finset.filter_congr fun a _ => by simp only [List.mem_dedup])
