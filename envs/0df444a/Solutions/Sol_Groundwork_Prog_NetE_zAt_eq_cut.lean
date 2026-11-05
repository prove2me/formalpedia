-- Prove2me | solution 1 for Groundwork.Prog.NetE.zAt_eq_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:28.478718+00:00
-- url     : https://prove2.me/submissions/e1bb819f-a16b-469c-8e8f-d8d6c4e3167f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_idxOf_map_inj
import Theorems.Thm_Groundwork_Prog_NetE_map_membersF
import Theorems.Thm_Groundwork_Prog_NetE_stLens_eq
import Theorems.Thm_Groundwork_cut_eq_getD


set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution (c : C) (x G : ℕ) (z : List Bool) (a : Fin g) :
    zAt K g Np c x G z a.val = cut (fun a : Fin g => Np.n c a.val) [] (membersF K x G) z a := by
  rw [cut_eq_getD, ← stLens_eq, zAt, ← map_membersF, idxOf_map_inj Fin.val_injective]
end Groundwork.Prog.NetE
