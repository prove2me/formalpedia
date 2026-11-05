-- Prove2me | solution 1 for Groundwork.Prog.NetE.nodup_prsF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:05:57.694351+00:00
-- url     : https://prove2.me/submissions/41b70a91-2f47-4b17-99c0-84a55bad8ed2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_nodup_membersF

set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution (x G G' : ℕ) : (prsF K x G G' : List (Fin g × Fin g)).Nodup := by
  have := (nodup_membersF (K := K) (g := g) x G).product (nodup_membersF (K := K) (g := g) x G')
  exact this
end Groundwork.Prog.NetE
