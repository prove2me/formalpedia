-- Prove2me | solution 1 for Groundwork.Prog.NetE.rowSum_le_Pc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:03:46.892136+00:00
-- url     : https://prove2.me/submissions/36b5b0ef-23bb-4657-8238-9ba88759f795

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_le_foldr_max_eth_NetVal_16a5ce4

set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (a : Fin g) : rowSum g Np c a.val ≤ Pc g Np c :=
  le_foldr_max_eth_NetVal_16a5ce4 (List.mem_map.2 ⟨a.val, List.mem_range.2 a.2, rfl⟩)
end Groundwork.Prog.NetE
