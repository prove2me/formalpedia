-- Prove2me | solution 1 for Groundwork.Prog.NetE.size_u_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:23.541201+00:00
-- url     : https://prove2.me/submissions/184618d7-fa8d-46d5-8978-ce05a4289308

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Theorems.Thm_Groundwork_Prog_NetE_sum_map_le
import Theorems.Thm_Groundwork_Prog_NetE_size_word
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
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
variable [HasSize C]
namespace Groundwork.Prog.NetE
theorem _root_.solution (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    size ((c, x), (G.val, List.ofFn θ)) ≤ size c + size x + size K + K * (2 * β + 2) + 1 := by
  have h1 : size (List.ofFn θ) ≤ K * (2 * β + 2) + 1 := by
    rw [size_list]
    have := sum_map_le (List.ofFn θ) (fun l => size l + 1) (2 * β + 2) (fun l hl => by
      obtain ⟨G', rfl⟩ : ∃ G', θ G' = l := by simpa [List.mem_ofFn] using hl
      rw [size_word]
      by_cases h : G' = G
      · rw [h, hG]; simp
      · rw [hθ G' h])
    rw [List.length_ofFn] at this
    omega
  have h2 : size G.val ≤ size K := by
    have := Nat.size_le_size G.2.le
    simp only [size_nat]; omega
  simp only [size_prod]
  omega
end Groundwork.Prog.NetE
