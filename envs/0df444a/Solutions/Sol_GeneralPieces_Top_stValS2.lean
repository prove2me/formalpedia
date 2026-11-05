-- Prove2me | solution 1 for GeneralPieces.Top.stValS2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:41:15.877695+00:00
-- url     : https://prove2.me/submissions/aa53e62e-d682-4440-974e-4598ade8a3e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Top_CaseI
import Theorems.Thm_GeneralPieces_Top_pow_le_two_pow
import Theorems.Thm_GeneralPieces_Top_Lof_le_of
import Theorems.Thm_GeneralPieces_Top_one_le_div
import Theorems.Thm_GeneralPieces_Top_val_caseI
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Top
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg CountKSat
namespace GeneralPieces.Top
theorem _root_.solution : StValS := by
  intro Idx _ S ok hS C F c pad i N Ub P B hi hK hN hSz hU hpad
  have hp : ∀ e, e ≤ needNet S i Ub P B → 2 ^ e ≤ pad.length := fun e he => (Nat.pow_le_pow_right (by norm_num) he).trans hpad
  have hK0 : 0 < S.K i := by omega
  unfold valS
  refine val_caseI S ok hS F c pad i N P B _ hi hK hN hSz (Lof_le_of hK0 hU) (by unfold lamS; rw [Nat.add_assoc]; exact one_le_div _ hK0) ?_ ?_ ?_ ?_ ?_
  · exact (pow_le_two_pow _ _).trans (hp _ ((le_max_left _ _).trans (le_max_left _ _)))
  · exact hp _ ((Nat.mul_le_mul_left _ (Nat.le_succ _)).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact hp _ ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact hp _ ((le_max_left _ _).trans (le_max_right _ _))
  · exact hp _ ((le_max_right _ _).trans (le_max_right _ _))
end GeneralPieces.Top
