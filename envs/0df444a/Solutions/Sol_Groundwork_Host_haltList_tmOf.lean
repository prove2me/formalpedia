-- Prove2me | solution 1 for Groundwork.Host.haltList_tmOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:59:13.351724+00:00
-- url     : https://prove2.me/submissions/426fafc7-fdfc-4d39-97be-2a25c5d0eb71

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
    @Eq (TM2.Cfg Γio H.Λ (Option Sym)) (haltList (tmOf H) x) ⟨none, none, withIO x (st [] [] [] [])⟩ := by
  unfold haltList
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl
end Groundwork.Host
