-- Prove2me | solution 1 for Groundwork.Host.within_io
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:47:32.23256+00:00
-- url     : https://prove2.me/submissions/5dc158c5-8e75-4943-8255-0fcdac9e76e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
import Theorems.Thm_Groundwork_TM_Frag_io_runs


set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
namespace Groundwork.Host
theorem _root_.solution {P : Fr} {S S' : Stk → List Sym} {t : ℕ} (h : P.Within S t S') (W : List Bool) :
    P.io.Within (withIO W S) t (withIO W S') := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn, Frag.io_runs hr W⟩
end Groundwork.Host
