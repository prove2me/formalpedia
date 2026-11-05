-- Prove2me | solution 1 for Groundwork.Host.skip_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:50:18.878852+00:00
-- url     : https://prove2.me/submissions/9e7d77f4-cbfe-4137-9227-333915ecbfda

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
import Theorems.Thm_Groundwork_TM_Frag_ofStmt_runs


set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
namespace Groundwork.Host
theorem _root_.solution (S : ∀ k, List (Γio k)) : skip.Runs none S 1 S := Frag.ofStmt_runs rfl
end Groundwork.Host
