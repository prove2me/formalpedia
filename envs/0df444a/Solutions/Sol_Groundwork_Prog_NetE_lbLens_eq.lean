-- Prove2me | solution 1 for Groundwork.Prog.NetE.lbLens_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:50.072626+00:00
-- url     : https://prove2.me/submissions/5af37c15-0917-4d54-b44f-f74321043ab0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_map_prsF

set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution (c : C) (x G G' : ℕ) :
    lbLens K g Np c x G G' = (prsF K x G G' : List (Fin g × Fin g)).map fun p => Np.cap c p.1.val p.2.val := by
  unfold lbLens
  rw [← map_prsF, List.map_map]
  rfl
end Groundwork.Prog.NetE
