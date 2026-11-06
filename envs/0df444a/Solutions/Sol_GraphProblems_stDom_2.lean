-- Prove2me | solution 2 for GraphProblems.stDom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:43.598792+00:00
-- url     : https://prove2.me/submissions/388c3bed-45c5-4d5b-a143-e438dcbfd0a6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Theorems.Thm_GraphProblems_Sets_cntS_eq_ncard
import Theorems.Thm_GraphProblems_Sets_sat_domF

set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open Sets
namespace GraphProblems
theorem _root_.solution : StDom := fun _ G s => cntS_eq_ncard s _ (fun S => IsDominating G S) (sat_domF G)
end GraphProblems
