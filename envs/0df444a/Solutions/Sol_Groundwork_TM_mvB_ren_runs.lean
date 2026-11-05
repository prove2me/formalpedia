-- Prove2me | solution 1 for Groundwork.TM.mvB_ren_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:12.018023+00:00
-- url     : https://prove2.me/submissions/d92b8fa6-1fea-4306-adb9-cf447855faa1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_mvB_runs
import Theorems.Thm_Groundwork_TM_toStk_injective
import Theorems.Thm_Groundwork_TM_Frag_ren_runs
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


attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd4_cnt

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
namespace Groundwork.TM
theorem _root_.solution (p₁ p₂ : Bool) {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : i ≠ .cnt)
    (hj : j ≠ .cnt) (hk : k ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym} (h : S i = code x ++ W) :
    ((mvB p₁ p₂).ren (toStk i j k)).Runs none S ((code x).length + 1)
      (Function.update (Function.update (Function.update S i W) j (putIf p₁ (mirror (code x)) (S j))) k
        (putIf p₂ (mirror (code x)) (S k))) := by
  refine Frag.ren_runs (toStk i j k) (toStk_injective hij hik hjk hi hj hk)
    (mvB_runs p₁ p₂ x W (S j) (S k) (S .cnt)) ?_ ?_ ?_
  · intro q
    cases q <;> simp [toStk, h]
  · intro q
    cases q <;> simp [toStk, hij, hik, hjk, hi.symm, hj.symm, hk.symm]
  · intro q hq
    have h1 : q ≠ i := fun e => hq .src e.symm
    have h2 : q ≠ j := fun e => hq .t1 e.symm
    have h3 : q ≠ k := fun e => hq .t2 e.symm
    simp [h1, h2, h3]
end Groundwork.TM
