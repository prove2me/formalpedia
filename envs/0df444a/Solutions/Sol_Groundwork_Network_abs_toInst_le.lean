-- Prove2me | solution 1 for Groundwork.Network.abs_toInst_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:05:40.750314+00:00
-- url     : https://prove2.me/submissions/ac43bda2-475d-40c8-aba1-0469335f9560

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_abs_prod_le_two_pow

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [DecidableEq A] (N : Network J σ τ)
    (D : J → J → Finset A) (dec : J → J → A → τ) {P B : ℕ} (h : N.Sized P B) (a : J) (θ : J → A) :
    |N.toInst D dec a θ| ≤ 2 ^ (P + B * Fintype.card J) := by
  unfold toInst
  have hJ : 0 < Fintype.card J := Fintype.card_pos_iff.2 ⟨a⟩
  have hcard : #(univ.erase a) ≤ Fintype.card J - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ a), Finset.card_univ]
  have hexp : B + B * (Fintype.card J - 1) = B * Fintype.card J := by
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card J = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hJ).symm⟩
    rw [hn, Nat.add_sub_cancel]; ring
  have h1 : ∀ z, |N.W a z * ∏ b ∈ univ.erase a, if θ b ∈ D (min a b) (max a b) then
      N.f a b z (dec (min a b) (max a b) (θ b)) else 0| ≤ 2 ^ (B * Fintype.card J) := by
    intro z
    rw [abs_mul, ← hexp, pow_add]
    refine mul_le_mul (h.abs_W a z) (abs_prod_le_two_pow _ _ (fun b _ => ?_) hcard) (abs_nonneg _)
      (pow_nonneg (by norm_num) _)
    split_ifs
    · exact h.abs_f _ _ _ _
    · simp
  calc _ ≤ ∑ z ∈ N.S a, |N.W a z * ∏ b ∈ univ.erase a, if θ b ∈ D (min a b) (max a b) then
      N.f a b z (dec (min a b) (max a b) (θ b)) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ N.S a, (2 : ℤ) ^ (B * Fintype.card J) := Finset.sum_le_sum fun z _ => h1 z
    _ = (#(N.S a) : ℤ) * 2 ^ (B * Fintype.card J) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ P * 2 ^ (B * Fintype.card J) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by norm_num) _)
          exact_mod_cast h.card_S a
    _ = 2 ^ (P + B * Fintype.card J) := (pow_add _ _ _).symm
end Groundwork.Network
