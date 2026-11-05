-- Prove2me | solution 1 for Groundwork.Prog.Count.sized_wordNet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:28:12.736301+00:00
-- url     : https://prove2.me/submissions/40d8293a-fe53-4647-9181-c6e51ab1a534

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_P2M_Groundwork_Prog_Count_wordNet___lt_709805682ec2
import Theorems.Thm_Groundwork_Prog_Count_wordNet_c
import Theorems.Thm_Groundwork_Prog_Count_le_mul_mu
import Theorems.Thm_Groundwork_Prog_Count_abs_boole_le
import Theorems.Thm_Groundwork_Prog_Count_lab_wordNet
import Theorems.Thm_Groundwork_SatNet_sized_net
import Theorems.Thm_Groundwork_card_words
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
import Theorems.Thm_P2M_Groundwork_Network___comm_f75ed8fe8218
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
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution (hg : 0 < g) (B : ℕ) : (wordNet g k φ).Sized (2 * k * mu g φ) B where
  card_S a := by
    simp only [wordNet, card_words]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_assoc, Nat.mul_comm k]; omega)
  abs_W a z := by
    simp only [wordNet, wF]
    exact (abs_boole_le _).trans (one_le_pow₀ (by norm_num))
  c_symm a b := by simp only [wordNet, capF, min_comm, max_comm]
  sum_c a := by
    rw [Finset.sum_congr rfl fun b _ => wordNet_c hg (le_mul_mu hg φ) a b]
    exact (sized_net (φ := φ) (g := g) (μ := mu g φ) (k := k) B).sum_c a
  card_lab a b _ := by
    rw [lab_wordNet, card_words]
    rfl
  abs_f a b z θ := by
    have h1 : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
    simp only [wordNet, fF]
    split_ifs <;> simp [h1]
  abs_Ψ a b z z' hab := by
    rcases lt_or_gt_of_ne hab with h | h
    · rw [wordNet_Ψ_lt h]; exact (abs_boole_le _).trans (one_le_pow₀ (by norm_num))
    · rw [Network.Ψ_comm, wordNet_Ψ_lt h]; exact (abs_boole_le _).trans (one_le_pow₀ (by norm_num))
end Groundwork.Prog.Count
