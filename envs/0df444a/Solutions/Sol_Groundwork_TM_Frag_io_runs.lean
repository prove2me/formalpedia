-- Prove2me | solution 1 for Groundwork.TM.Frag.io_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:17.946644+00:00
-- url     : https://prove2.me/submissions/391b73c3-a709-4cc8-81e9-8dee46bd5a67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_Machine_Lift
import Theorems.Thm_Groundwork_TM_run_liftIO

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
namespace Groundwork.TM
namespace Frag
theorem _root_.solution {P : Fr} {v : Option Sym} {S S' : Stk → List Sym} {n : ℕ} (h : P.Runs v S n S') (W : List Bool) :
    P.io.Runs v (withIO W S) n (withIO W S') :=
  run_liftIO W h
end Frag
end Groundwork.TM
