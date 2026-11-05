-- Prove2me | solution 1 for Groundwork.Prog.size_list_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:40.73783+00:00
-- url     : https://prove2.me/submissions/4f006830-ef3c-47a5-abb9-9de784db91e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Prog_Sat
import Theorems.Thm_Groundwork_Prog_sum_size_le
import Theorems.Thm_Groundwork_size_list
attribute [local simp] Groundwork.size_list



set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Groundwork.Sparsify (leaves rootP stepP)
namespace Groundwork.Prog
theorem _root_.solution {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k)
    (hs : ∀ x ∈ l, size x ≤ s) : size l ≤ k * (s + 1) + 1 := by
  rw [size_list]
  exact Nat.succ_le_succ ((sum_size_le l hs).trans (Nat.mul_le_mul_right _ hl))
end Groundwork.Prog
