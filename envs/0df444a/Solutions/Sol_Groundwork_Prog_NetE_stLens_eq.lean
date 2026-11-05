-- Prove2me | solution 1 for Groundwork.Prog.NetE.stLens_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:05:58.859051+00:00
-- url     : https://prove2.me/submissions/6f335b30-5505-4df0-b1d6-0469afc252f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_map_membersF

set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution (c : C) (x G : ℕ) :
    stLens K g Np c x G = (membersF K x G : List (Fin g)).map fun a => Np.n c a.val := by
  unfold stLens
  rw [← map_membersF, List.map_map]
  rfl
end Groundwork.Prog.NetE
