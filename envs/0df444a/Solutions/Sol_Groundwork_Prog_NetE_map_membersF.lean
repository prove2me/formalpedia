-- Prove2me | solution 1 for Groundwork.Prog.NetE.map_membersF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:57.906557+00:00
-- url     : https://prove2.me/submissions/e6693eef-b766-4b26-8bce-82eb3a192b75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal

set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution (x G : ℕ) : (membersF K x G : List (Fin g)).map Fin.val = members K g x G := by
  unfold membersF members
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  rfl
end Groundwork.Prog.NetE
