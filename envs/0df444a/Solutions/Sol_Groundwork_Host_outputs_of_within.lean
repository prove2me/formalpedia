-- Prove2me | solution 1 for Groundwork.Host.outputs_of_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:11.407917+00:00
-- url     : https://prove2.me/submissions/0cf3e7c4-4dc5-4275-ac5f-cc81687e7a00

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
import Theorems.Thm_Groundwork_Host_initList_tmOf
import Theorems.Thm_Groundwork_Host_haltList_tmOf
import Theorems.Thm_Groundwork_Stepped_Reaches_iterate
import Theorems.Thm_Groundwork_TM_Run_iterate


set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
namespace Groundwork.Host
theorem _root_.solution {H : FrIO} {x y : List Bool} {t : ℕ}
    (h : Frag.Within H (withIO x (st [] [] [] [])) t (withIO y (st [] [] [] []))) {x' y' : List Bool} (hx : x' = x)
    (hy : y' = y) : Nonempty (TM2OutputsInTime (tmOf H) x' (some y') t) := by
  subst hx hy
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨⟨⟨n, ?_⟩, hn⟩⟩
  have e := hr.iterate
  rw [← initList_tmOf H x', ← haltList_tmOf H y'] at e
  exact e
end Groundwork.Host
