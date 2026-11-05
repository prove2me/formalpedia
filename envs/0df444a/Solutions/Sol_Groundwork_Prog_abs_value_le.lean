-- Prove2me | solution 1 for Groundwork.Prog.abs_value_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:33:15.05242+00:00
-- url     : https://prove2.me/submissions/3c7c248c-79b6-4969-b4e7-e99e2d373918

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_GridLoop
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
section
open Groundwork Groundwork.Prog
open Finset Stepped
namespace Groundwork.Prog
theorem _root_.solution {J σ τ : Type} [Fintype J] [LinearOrder J] (N : Network J σ τ) {P B : ℕ}
    (h : N.Sized P B) : |N.value| ≤ 2 ^ (Fintype.card J * (P + B) + Fintype.card J * Fintype.card J * B) := by
  unfold Network.value
  have hW : ∀ z : J → σ, |∏ a, N.W a (z a)| ≤ (2 ^ B) ^ Fintype.card J := by
    intro z
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _a : J, (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun a _ => h.abs_W a _
      _ = _ := by rw [Finset.prod_const, card_univ]
  have hcard : #(pairs J) ≤ Fintype.card J * Fintype.card J := by
    refine (Finset.card_le_univ _).trans ?_
    rw [Fintype.card_prod]
  have hΨ : ∀ z : J → σ, |∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)| ≤ (2 ^ B) ^ (Fintype.card J * Fintype.card J) := by
    intro z
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _p ∈ pairs J, (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p hp =>
          h.abs_Ψ _ _ _ _ (ne_of_lt (by simpa [pairs] using hp))
      _ = ((2 : ℤ) ^ B) ^ #(pairs J) := by rw [Finset.prod_const]
      _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hcard
  have hS : (#(Fintype.piFinset N.S) : ℤ) ≤ (2 ^ P) ^ Fintype.card J := by
    rw [Fintype.card_piFinset]
    have : ∏ a, #(N.S a) ≤ ∏ _a : J, 2 ^ P := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ => h.card_S a
    rw [Finset.prod_const, card_univ] at this
    exact_mod_cast this
  calc _ ≤ ∑ z ∈ Fintype.piFinset N.S, |(∏ a, N.W a (z a)) * ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ Fintype.piFinset N.S,
          ((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ (Fintype.card J * Fintype.card J) := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hW z) (hΨ z) (abs_nonneg _) (by positivity)
    _ = (#(Fintype.piFinset N.S) : ℤ)
          * (((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ (Fintype.card J * Fintype.card J)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ P) ^ Fintype.card J
          * (((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ (Fintype.card J * Fintype.card J)) :=
        mul_le_mul_of_nonneg_right hS (by positivity)
    _ = _ := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
end Groundwork.Prog
