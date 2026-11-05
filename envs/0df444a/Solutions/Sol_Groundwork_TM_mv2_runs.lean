-- Prove2me | solution 1 for Groundwork.TM.mv2_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:44.339467+00:00
-- url     : https://prove2.me/submissions/b4c61492-8be9-4c14-8a27-3e02fe95cb7a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move
import Theorems.Thm_Groundwork_TM_mvB_ren_runs

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
namespace Groundwork.TM
theorem _root_.solution {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : i ≠ .cnt) (hj : j ≠ .cnt) (hk : k ≠ .cnt)
    (x : V) {S : Stk → List Sym} {W : List Sym} (h : S i = code x ++ W) :
    (mv2 i j k).Runs none S ((code x).length + 1)
      (Function.update (Function.update (Function.update S i W) j (mirror (code x) ++ S j)) k (mirror (code x) ++ S k)) :=
  mvB_ren_runs true true hij hik hjk hi hj hk x h
end Groundwork.TM
