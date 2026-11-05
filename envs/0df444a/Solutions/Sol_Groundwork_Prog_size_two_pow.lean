-- Prove2me | solution 1 for Groundwork.Prog.size_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:05:34.552073+00:00
-- url     : https://prove2.me/submissions/60f09a52-4643-4ccf-9e75-59809ca2b29e

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
theorem _root_.solution (k : ℕ) : size (2 ^ k) = k + 2 := by
  rw [size_nat, Nat.size_pow]
end Groundwork.Prog
