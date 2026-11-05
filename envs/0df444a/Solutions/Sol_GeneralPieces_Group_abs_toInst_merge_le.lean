-- Prove2me | solution 1 for GeneralPieces.Group.abs_toInst_merge_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:51:56.925056+00:00
-- url     : https://prove2.me/submissions/1c292cd7-8335-419f-8d1f-4edcc5729ae6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma
import Theorems.Thm_GeneralPieces_Group_card_values_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_Network_merge_shaped
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_abs_prod_le_two_pow
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
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.TM.update_withIO
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
open GeneralPieces GeneralPieces.Group
open Finset Groundwork
variable {J J' σ τ A : Type*}
namespace GeneralPieces.Group
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] [DecidableEq A] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    (D : J' → J' → Finset A) (dec : J' → J' → A → (J × J → τ)) {P B m : ℕ} (h : N.Sized P B) (hm : ∀ G, #{a | χ a = G} ≤ m) (G : J') (θ : J' → A) :
    |(N.merge χ s₀ t₀).toInst D dec G θ| ≤ 2 ^ (P * m + B * Fintype.card J ^ 2) := by
  have hSh := Network.merge_shaped N χ s₀ t₀ h.toShaped hm
  unfold Network.toInst
  have h1 : ∀ z, |(N.merge χ s₀ t₀).W G z * ∏ b ∈ univ.erase G, if θ b ∈ D (min G b) (max G b) then
      (N.merge χ s₀ t₀).f G b z (dec (min G b) (max G b) (θ b)) else 0| ≤ 2 ^ (B * Fintype.card J ^ 2) := by
    intro z
    have w1 : |(N.merge χ s₀ t₀).W G z| ≤ 2 ^ (B * #{a | χ a = G}) * 2 ^ (B * #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G}) := by
      simp only [Network.merge]
      rw [abs_mul]
      refine mul_le_mul (abs_prod_le_two_pow _ _ (fun a _ => h.abs_W a _) le_rfl)
        (abs_prod_le_two_pow _ _ (fun p hp => h.abs_Ψ _ _ _ _ ?_) le_rfl) (abs_nonneg _) (pow_nonneg (by norm_num) _)
      have : p.1 < p.2 := by simpa [pairs] using (Finset.mem_filter.1 hp).1
      exact this.ne
    have w2 : |∏ b ∈ univ.erase G, if θ b ∈ D (min G b) (max G b) then
        (N.merge χ s₀ t₀).f G b z (dec (min G b) (max G b) (θ b)) else 0| ≤ 2 ^ (B * ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'}) := by
      rw [Finset.abs_prod, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun b _ => ?_
      split_ifs
      · simp only [Network.merge]
        exact abs_prod_le_two_pow _ _ (fun p _ => h.abs_f _ _ _ _) le_rfl
      · simp
    calc _ = |(N.merge χ s₀ t₀).W G z| * |∏ b ∈ univ.erase G, if θ b ∈ D (min G b) (max G b) then
          (N.merge χ s₀ t₀).f G b z (dec (min G b) (max G b) (θ b)) else 0| := abs_mul _ _
      _ ≤ 2 ^ (B * #{a | χ a = G}) * 2 ^ (B * #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G}) *
          2 ^ (B * ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'}) := mul_le_mul w1 w2 (abs_nonneg _) (by positivity)
      _ = 2 ^ (B * (#{a | χ a = G} + #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G} + ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'})) := by
          rw [← pow_add, ← pow_add, ← mul_add, ← mul_add]
      _ ≤ 2 ^ (B * Fintype.card J ^ 2) := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (card_values_le χ G))
  calc _ ≤ ∑ z ∈ (N.merge χ s₀ t₀).S G, |(N.merge χ s₀ t₀).W G z * ∏ b ∈ univ.erase G, if θ b ∈ D (min G b) (max G b) then
      (N.merge χ s₀ t₀).f G b z (dec (min G b) (max G b) (θ b)) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ (N.merge χ s₀ t₀).S G, (2 : ℤ) ^ (B * Fintype.card J ^ 2) := Finset.sum_le_sum fun z _ => h1 z
    _ = (#((N.merge χ s₀ t₀).S G) : ℤ) * 2 ^ (B * Fintype.card J ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (P * m) * 2 ^ (B * Fintype.card J ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by norm_num) _)
          exact_mod_cast hSh.card_S G
    _ = 2 ^ (P * m + B * Fintype.card J ^ 2) := (pow_add _ _ _).symm
end GeneralPieces.Group
