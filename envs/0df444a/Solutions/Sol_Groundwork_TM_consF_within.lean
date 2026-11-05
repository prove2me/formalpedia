-- Prove2me | solution 1 for Groundwork.TM.consF_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:51:44.458486+00:00
-- url     : https://prove2.me/submissions/c55e40d0-2289-4772-9a16-a483b1cd5358

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Move
import Definitions.Def_ToTuring_TM_Ops
import Theorems.Thm_Groundwork_TM_pushW_within
import Theorems.Thm_Groundwork_TM_toA_within
import Theorems.Thm_Groundwork_TM_toB_within
import Theorems.Thm_Groundwork_TM_fromA_within
import Theorems.Thm_Groundwork_TM_fromB_within
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main



set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable (x y : V) (M A B N : List Sym)
namespace Groundwork.TM
theorem _root_.solution : consF.Within (st (code x ++ (code y ++ M)) A B N) (2 * ((code x).length + (code y).length) + 6)
    (st (code (.cons x y) ++ M) A B N) := by
  have h1 := toA_within x (code y ++ M) A B N
  have h2 := toB_within y M (mirror (code x) ++ A) B N
  have h3 := pushW_within M (mirror (code x) ++ A) (mirror (code y) ++ B) N [.R]
  have h4 := fromB_within y ([.R] ++ M) (mirror (code x) ++ A) B N
  have h5 := fromA_within x (code y ++ ([.R] ++ M)) A B N
  have h6 := pushW_within (code x ++ (code y ++ ([.R] ++ M))) A B N [.L]
  have e : [Sym.L] ++ (code x ++ (code y ++ ([.R] ++ M))) = code (.cons x y) ++ M := by simp [code]
  rw [e] at h6
  exact (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).mono (by omega)
end Groundwork.TM
