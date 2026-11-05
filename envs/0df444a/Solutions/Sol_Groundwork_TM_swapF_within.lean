-- Prove2me | solution 1 for Groundwork.TM.swapF_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:52:53.565964+00:00
-- url     : https://prove2.me/submissions/2dd457f3-097e-4a44-9165-cb7e6952740c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Move
import Definitions.Def_ToTuring_TM_Ops
import Theorems.Thm_Groundwork_TM_toA_within
import Theorems.Thm_Groundwork_TM_toB_within
import Theorems.Thm_Groundwork_TM_fromA_within
import Theorems.Thm_Groundwork_TM_fromB_within
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq


set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable (x y : V) (M A B N : List Sym)
namespace Groundwork.TM
theorem _root_.solution : swapF.Within (st (code x ++ (code y ++ M)) A B N) (2 * ((code x).length + (code y).length) + 4)
    (st (code y ++ (code x ++ M)) A B N) := by
  have h1 := toA_within x (code y ++ M) A B N
  have h2 := toB_within y M (mirror (code x) ++ A) B N
  have h3 := fromA_within x M A (mirror (code y) ++ B) N
  have h4 := fromB_within y (code x ++ M) A B N
  exact (((h1.seq h2).seq h3).seq h4).mono (by omega)
end Groundwork.TM
