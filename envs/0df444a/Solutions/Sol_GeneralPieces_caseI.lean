-- Prove2me | solution 1 for GeneralPieces.caseI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:42:33.905108+00:00
-- url     : https://prove2.me/submissions/481bbfb4-77e0-4deb-a617-e87eaf975939

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_CaseI
import Theorems.Thm_Groundwork_Colouring_exists_colouring
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_TM_Run_trans
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
open GeneralPieces
open Finset
namespace GeneralPieces
theorem _root_.solution (K g : ℕ) (c : Fin g → Fin g → ℕ) (P ζ : ℝ) (hK : 2 ≤ K) (hg : g = 3 * K ^ 8) (hζ : ζ = 1 / (2 * K)) (hs : ∀ a b, c a b = c b a)
    (hP : ∀ a, ∑ b ∈ univ.erase a, (c a b : ℝ) ≤ P) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) ≤
        ((∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + 2 * ζ * g * P) / (K : ℝ) ^ 2 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hg0 : 0 < g := by rw [hg]; positivity
  have her : ∀ a : Fin g, ({b | b ≠ a} : Finset (Fin g)) = univ.erase a := fun a => by
    ext b; simp
  have hP0 : 0 ≤ P := le_trans (sum_nonneg fun _ _ => Nat.cast_nonneg _) (hP ⟨0, hg0⟩)
  obtain ⟨χ, h1, h2⟩ := Groundwork.Colouring.exists_colouring hK hg.ge c hs ⌊P⌋₊ fun a => by
    rw [her]
    exact Nat.le_floor (by push_cast; exact hP a)
  refine ⟨χ, h1, fun γ γ' hne => ?_⟩
  have h3 := h2 γ γ' hne
  simp only [her] at h3
  have h4 : (K : ℝ) ^ 3 * (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) ≤
      K * (∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + g * (⌊P⌋₊ : ℝ) := by exact_mod_cast h3
  have h5 : (g : ℝ) * (⌊P⌋₊ : ℝ) ≤ g * P := mul_le_mul_of_nonneg_left (Nat.floor_le hP0) (Nat.cast_nonneg _)
  rw [hζ, le_div_iff₀ (by positivity)]
  have e : (∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + 2 * (1 / (2 * (K : ℝ))) * g * P =
      (K * (∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + g * P) / K := by field_simp
  rw [e, le_div_iff₀ hK0]
  calc (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) * (K : ℝ) ^ 2 * K
      = (K : ℝ) ^ 3 * (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) := by ring
    _ ≤ _ := h4.trans (by linarith)
end GeneralPieces
