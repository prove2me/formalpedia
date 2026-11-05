-- Prove2me | solution 1 for Groundwork.Prog.NetE.div_mod_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:29.607197+00:00
-- url     : https://prove2.me/submissions/590ae00e-3f83-497e-8de2-639fcaa83094

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
theorem _root_.solution (a b : Fin g) : (a.val * g + b.val) / g = a.val ∧ (a.val * g + b.val) % g = b.val := by
  have hg : 0 < g := a.pos
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt b.2, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.2]
end Groundwork.Prog.NetE
