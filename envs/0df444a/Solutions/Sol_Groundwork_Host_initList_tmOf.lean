-- Prove2me | solution 1 for Groundwork.Host.initList_tmOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:59:11.82601+00:00
-- url     : https://prove2.me/submissions/b97a7740-b48e-4664-87f9-ff2b05b059b9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
namespace Groundwork.Host
theorem _root_.solution (H : FrIO) (x : List Bool) :
    @Eq (TM2.Cfg Γio H.Λ (Option Sym)) (initList (tmOf H) x) ⟨some H.entry, none, withIO x (st [] [] [] [])⟩ := by
  unfold initList
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl
end Groundwork.Host
