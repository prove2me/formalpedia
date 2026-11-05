-- Prove2me | solution 1 for Groundwork.Prog.NetE.nodup_membersF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:59:52.445074+00:00
-- url     : https://prove2.me/submissions/d75d370e-2c9b-41c6-899e-e4b6b8c01011

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
theorem _root_.solution (x G : ℕ) : (membersF K x G : List (Fin g)).Nodup :=
  (List.nodup_finRange g).filter _
end Groundwork.Prog.NetE
