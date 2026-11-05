-- Prove2me | solution 1 for Groundwork.TM.stepAux_liftIO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:08.423825+00:00
-- url     : https://prove2.me/submissions/0b9512d1-7503-46df-a594-120a781ac46f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_Machine_Lift
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main


attribute [local simp] Groundwork.TM.update_withIO

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
namespace Groundwork.TM
theorem _root_.solution {Λ σ : Type} (W : List Bool) (q : TM2.Stmt (fun _ : Stk => Sym) Λ σ) (v : σ) (S : Stk → List Sym) :
    TM2.stepAux (liftIO q) v (withIO W S) = liftCfg W (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simp only [liftIO, TM2.stepAux, update_withIO]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => simp only [liftIO, TM2.stepAux, update_withIO]; exact ih _ _
  | load f q ih => exact ih _ _
  | branch p q₁ q₂ ih₁ ih₂ => simp only [liftIO, TM2.stepAux, ih₁, ih₂]; cases p v <;> rfl
  | goto l => rfl
  | halt => rfl
end Groundwork.TM
