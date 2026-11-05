-- Prove2me | solution 1 for Groundwork.TM.drp_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:47:01.587365+00:00
-- url     : https://prove2.me/submissions/5f137924-ba40-471a-81d1-6a8a023b6e9f

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
import Theorems.Thm_Groundwork_TM_mvB_ren_runs
import Theorems.Thm_Groundwork_TM_other_ne
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
theorem _root_.solution {i : Stk} (hi : i ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym} (h : S i = code x ++ W) :
    (drp i).Runs none S ((code x).length + 1) (Function.update S i W) := by
  obtain ⟨h1, -, h3⟩ := other_ne i i
  obtain ⟨k1, k2, k3⟩ := other_ne i (other i i)
  have r := mvB_ren_runs false false h1.symm k1.symm k2.symm hi h3 k3 x h
  have e : Function.update (Function.update (Function.update S i W) (other i i)
      (putIf false (mirror (code x)) (S (other i i)))) (other i (other i i))
      (putIf false (mirror (code x)) (S (other i (other i i)))) = Function.update S i W := by
    funext q
    by_cases hq : q = other i (other i i)
    · subst hq; simp [putIf, k1]
    · by_cases hq' : q = other i i
      · subst hq'; simp [putIf, h1, hq]
      · simp [Function.update_apply, putIf, hq, hq']
  rw [e] at r
  exact r
end Groundwork.TM
