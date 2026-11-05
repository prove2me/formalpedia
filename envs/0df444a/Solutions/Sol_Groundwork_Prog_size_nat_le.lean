-- Prove2me | solution 1 for Groundwork.Prog.size_nat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:29:13.544451+00:00
-- url     : https://prove2.me/submissions/45bdcd39-843e-42f6-a899-12062faa3007

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_SideBasics
import Theorems.Thm_Groundwork_size_nat
attribute [local simp] Groundwork.size_nat



set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
namespace Groundwork.Prog
theorem _root_.solution (n : ℕ) : size n ≤ n + 1 := by
  rw [size_nat]
  exact Nat.succ_le_succ (Nat.size_le.2 Nat.lt_two_pow_self)
end Groundwork.Prog
