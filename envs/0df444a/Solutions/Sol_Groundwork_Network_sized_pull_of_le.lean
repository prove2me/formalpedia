-- Prove2me | solution 1 for Groundwork.Network.sized_pull_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:16:29.068589+00:00
-- url     : https://prove2.me/submissions/b27c253c-70d4-479a-bd8d-2a5552e4d752

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Definitions.Def_StepMachines_Math_Pull
import Theorems.Thm_P2M_Groundwork_Network___pull_e5947ed64801
import Theorems.Thm_Groundwork_Network_lab_pull
import Theorems.Thm_Groundwork_card_words
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
theorem _root_.solution {P B : ℕ} (h : N.Sized P B) (hn : ∀ a, n a ≤ P) : (N.pull n cs cl).Sized P B := by
  refine ⟨⟨fun a => ?_, h.c_symm, h.sum_c, fun a b _ => ?_⟩, fun a z => h.abs_W _ _, fun a b z θ => ?_,
    fun a b z z' hab => ?_⟩
  · change #(words (n a)) ≤ 2 ^ P
    rw [card_words]
    exact Nat.pow_le_pow_right (by norm_num) (hn a)
  · rw [lab_pull N n cs cl h, card_words]
    exact le_rfl
  · simp only [pull]
    split_ifs
    · exact h.abs_f _ _ _ _
    · simp
  · rw [Ψ_pull]
    exact h.abs_Ψ _ _ _ _ hab
end Groundwork.Network
