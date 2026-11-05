-- Prove2me | solution 1 for Groundwork.Prog.NetE.mem_prs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:59:34.261375+00:00
-- url     : https://prove2.me/submissions/da2d2880-fc9f-49bc-a743-7f5ba720d299

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun

set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution {x G G' a b : ℕ} (ha : a ∈ members K g x G) (hb : b ∈ members K g x G') :
    (a, b) ∈ prs K g x G G' :=
  List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, hb, rfl⟩⟩
end Groundwork.Prog.NetE
