-- Prove2me | solution 1 for Groundwork.Code.full_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:24.280563+00:00
-- url     : https://prove2.me/submissions/6ea03753-7b95-48bb-bc3c-5d68490c95e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore
import Theorems.Thm_Groundwork_length_block
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (pos : ι ≃ Fin r) {m : ℕ} (c : Code S m)
    (h : c.Full) : (blocks pos c).Full := by
  refine filter_true_of_mem fun w hw i => ?_
  rw [h, mem_words]
  refine length_block ?_
  rw [mem_words.1 hw]
  exact Nat.mul_le_mul_right _ (pos i).2
end Groundwork.Code
