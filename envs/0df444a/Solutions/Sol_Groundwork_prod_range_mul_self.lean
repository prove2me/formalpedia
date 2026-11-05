-- Prove2me | solution 1 for Groundwork.prod_range_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:27.448055+00:00
-- url     : https://prove2.me/submissions/2c78d943-f206-4377-82f1-e0577f920ff1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution (g : ℕ) (F : ℕ → ℤ) :
    ∏ i ∈ range (g * g), F i = ∏ p : Fin g × Fin g, F (p.1.val * g + p.2.val) := by
  rw [Finset.prod_range, ← Fintype.prod_equiv finProdFinEquiv (fun p : Fin g × Fin g => F (p.1.val * g + p.2.val))
    (fun i : Fin (g * g) => F i.val)]
  intro p
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
end Groundwork
