-- Prove2me | solution 1 for Groundwork.TM.run_liftIO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:11.230703+00:00
-- url     : https://prove2.me/submissions/1beaf01b-af76-430e-8064-60b9fdcd769b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_Machine_Lift
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_TM_stepAux_liftIO
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
theorem _root_.solution {Λ σ : Type} (W : List Bool) {M : Λ → TM2.Stmt (fun _ : Stk => Sym) Λ σ} :
    ∀ {n : ℕ} {a b : TM2.Cfg (fun _ : Stk => Sym) Λ σ}, Run (TM2.step M) a n b →
      Run (TM2.step fun l => liftIO (M l)) (liftCfg W a) n (liftCfg W b)
  | 0, _, _, h => by cases h; exact rfl
  | n + 1, ⟨none, v, S⟩, b, ⟨c, hc, _⟩ => by simp [TM2.step] at hc
  | n + 1, ⟨some l, v, S⟩, b, ⟨c, hc, h⟩ => by
    refine ⟨liftCfg W c, ?_, solution W h⟩
    simp only [TM2.step, Option.some.injEq] at hc
    simp only [liftCfg, TM2.step, stepAux_liftIO, hc]
end Groundwork.TM
