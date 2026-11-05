-- Prove2me | solution 1 for Groundwork.Prog.NetE.stLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:59:51.127268+00:00
-- url     : https://prove2.me/submissions/92945f22-7355-4c2d-9228-2fa8c3c84209

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Theorems.Thm_Groundwork_Prog_NetE_mem_members
import Theorems.Thm_Groundwork_Prog_NetE_sum_map_le
import Theorems.Thm_Groundwork_Prog_NetE_n_le

set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hN : Np.Presents c N t S) (hS : N.Sized P B) {x G m : ℕ}
    (hm : (members K g x G).length ≤ m) : stLen K g Np c x G ≤ P * m := by
  unfold stLen stLens
  refine (sum_map_le _ _ P fun a ha => ?_).trans ?_
  · exact n_le hN hS ⟨a, ((mem_members K g).1 ha).1⟩
  · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hm
end Groundwork.Prog.NetE
