-- Prove2me | solution 2 for GraphProblems.stIndep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:42.531964+00:00
-- url     : https://prove2.me/submissions/377fe172-9d00-4923-883c-facf98e7fb0c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Theorems.Thm_GraphProblems_Sets_cntS_eq_ncard
import Theorems.Thm_GraphProblems_Sets_sat_indepF
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open Sets
namespace GraphProblems
theorem _root_.solution : StIndep := fun n G s => by
  rw [cntS_eq_ncard s _ (fun S => G.IsIndepSet (S : Set (Fin n))) (sat_indepF G), numIndepSets]
  congr 1
  ext S
  exact (G.isNIndepSet_iff s S).symm
end GraphProblems
