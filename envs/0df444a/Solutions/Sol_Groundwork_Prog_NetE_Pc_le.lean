-- Prove2me | solution 1 for Groundwork.Prog.NetE.Pc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:09:36.412737+00:00
-- url     : https://prove2.me/submissions/de3b49bd-6ff9-429a-b156-d3bb124a35dd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_foldr_max_le
import Theorems.Thm_Groundwork_Prog_NetE_rowSum_eq

set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hN : Np.Presents c N t S) {P B : ℕ} (hS : N.Sized P B) : Pc g Np c ≤ P := by
  refine foldr_max_le fun r hr => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
  rw [rowSum_eq Np hN ⟨a, List.mem_range.1 ha⟩]
  exact hS.sum_c _
end Groundwork.Prog.NetE
