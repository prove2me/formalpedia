-- Prove2me | solution 1 for Groundwork.Network.value_pull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:14:44.094544+00:00
-- url     : https://prove2.me/submissions/458c5203-8005-4d8b-9bad-2428b87d9dbe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Definitions.Def_StepMachines_Math_Pull
import Theorems.Thm_P2M_Groundwork_Network___pull_e5947ed64801
import Theorems.Thm_Groundwork_Network_sum_pi_dec
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Network
variable {J σ τ : Type*}
variable [Fintype J] [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
  (cl : ∀ a b, Code (N.Θ a b) (N.c a b))
namespace Groundwork.Network
theorem _root_.solution (h : ∀ a, (cs a).Full) : (N.pull n cs cl).value = N.value := by
  unfold value
  simp only [Ψ_pull]
  rw [← sum_pi_dec n cs]
  have hS : (N.pull n cs cl).S = fun a => (cs a).D := funext fun a => (h a).symm
  rw [hS]
  rfl
end Groundwork.Network
