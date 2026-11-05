-- Prove2me | solution 1 for GeneralPieces.Group.exists_no_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:25.776473+00:00
-- url     : https://prove2.me/submissions/1f8e75e5-2654-49f6-878a-a1cce497baf2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_GeneralPieces_Group_exp_le_inv
import Theorems.Thm_GeneralPieces_Group_event_first_kind
import Theorems.Thm_GeneralPieces_Group_event_second_kind
import Theorems.Thm_GeneralPieces_Group_card_events_lt
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
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (hK : 1 ≤ K) (hn : 1 ≤ n) (hg : 2 ≤ K * n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (hζ : 0 ≤ ζ) (hP0 : 0 < P)
    (hP : ∀ a, cs c a ≤ P) (hPg : ∀ a b, a ≠ b → (c a b : ℝ) ≤ P / ((K * n : ℕ) : ℝ))
    (hH : (K : ℝ) * Real.log (2 * ((K * n : ℕ) : ℝ) * K) ≤ 2 * ζ ^ 2 * ((K * n : ℕ) : ℝ)) :
    ∃ e : Equiv.Perm (Fin (K * n)), (∀ γ, ∑ a ∈ cls e γ, cs c a < (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K) ∧
      ∀ a γ', ∑ b ∈ cls e γ', cz c a b < (cs c a + ζ * P) / K := by
  by_contra hno
  push Not at hno
  obtain ⟨ε, hε⟩ : ∃ ε, ε = Real.exp (-(2 * n * ζ ^ 2)) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = #(univ : Finset (Equiv.Perm (Fin (K * n)))) := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast card_pos.2 univ_nonempty
  have hε0 : 0 < ε := by rw [hε]; exact Real.exp_pos _
  have hε1 : ε ≤ 1 / (2 * ((K * n : ℕ) : ℝ) * K) := by rw [hε]; exact exp_le_inv hK hn hH
  obtain ⟨E1, hE1⟩ : ∃ E1 : Fin K → Finset (Equiv.Perm (Fin (K * n))),
      ∀ γ, E1 γ = ({e | (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K ≤ ∑ a ∈ cls e γ, cs c a} : Finset (Equiv.Perm (Fin (K * n)))) := ⟨_, fun _ => rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2 : Fin (K * n) → Fin K → Finset (Equiv.Perm (Fin (K * n))),
      ∀ a γ', E2 a γ' = ({e | (cs c a + ζ * P) / K ≤ ∑ b ∈ cls e γ', cz c a b} : Finset (Equiv.Perm (Fin (K * n)))) := ⟨_, fun _ _ => rfl⟩
  have h1 : ∀ γ, (#(E1 γ) : ℝ) ≤ ε * N := fun γ => by rw [hE1, hε, hN]; exact event_first_kind hK hn c hζ hP0 hP γ
  have h2 : ∀ a γ', (#(E2 a γ') : ℝ) ≤ ε * N := fun a γ' => by rw [hE2, hε, hN]; exact event_second_kind hK hn c hζ hP0 hPg a γ'
  have hcover : (univ : Finset (Equiv.Perm (Fin (K * n)))) ⊆ (univ.biUnion E1) ∪ (univ.biUnion fun a => univ.biUnion (E2 a)) := by
    intro e _
    by_cases h : ∀ γ, ∑ a ∈ cls e γ, cs c a < (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K
    · obtain ⟨a, γ', hb⟩ := hno e h
      exact mem_union_right _ (mem_biUnion.2 ⟨a, mem_univ _, mem_biUnion.2 ⟨γ', mem_univ _, by rw [hE2]; exact mem_filter.2 ⟨mem_univ _, hb⟩⟩⟩)
    · push Not at h
      obtain ⟨γ, hγ⟩ := h
      exact mem_union_left _ (mem_biUnion.2 ⟨γ, mem_univ _, by rw [hE1]; exact mem_filter.2 ⟨mem_univ _, hγ⟩⟩)
  have hcard : N ≤ ∑ γ, (#(E1 γ) : ℝ) + ∑ a, ∑ γ', (#(E2 a γ') : ℝ) := by
    have := (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add card_biUnion_le (card_biUnion_le.trans (sum_le_sum fun a _ => card_biUnion_le))))
    rw [hN]
    exact_mod_cast this
  have hb1 : ∑ γ, (#(E1 γ) : ℝ) ≤ K * (ε * N) := by
    calc ∑ γ, (#(E1 γ) : ℝ) ≤ ∑ _γ : Fin K, ε * N := sum_le_sum fun γ _ => h1 γ
      _ = K * (ε * N) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb2 : ∑ a, ∑ γ', (#(E2 a γ') : ℝ) ≤ ((K * n : ℕ) : ℝ) * (K * (ε * N)) := by
    calc ∑ a, ∑ γ', (#(E2 a γ') : ℝ) ≤ ∑ _a : Fin (K * n), ∑ _γ : Fin K, ε * N := sum_le_sum fun a _ => sum_le_sum fun γ' _ => h2 a γ'
      _ = ((K * n : ℕ) : ℝ) * (K * (ε * N)) := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hev : (((K * n : ℕ) : ℝ) + 1) * K < 2 * ((K * n : ℕ) : ℝ) * K := by exact_mod_cast card_events_lt hK hg
  have hpos : (0 : ℝ) < 2 * ((K * n : ℕ) : ℝ) * K := lt_of_le_of_lt (by positivity) hev
  have h3 : (((K * n : ℕ) : ℝ) + 1) * K * ε < 1 := by
    calc (((K * n : ℕ) : ℝ) + 1) * K * ε < 2 * ((K * n : ℕ) : ℝ) * K * ε := mul_lt_mul_of_pos_right hev hε0
      _ ≤ 2 * ((K * n : ℕ) : ℝ) * K * (1 / (2 * ((K * n : ℕ) : ℝ) * K)) := mul_le_mul_of_nonneg_left hε1 hpos.le
      _ = 1 := mul_one_div_cancel hpos.ne'
  have h4 : N ≤ (((K * n : ℕ) : ℝ) + 1) * K * ε * N := by
    calc N ≤ K * (ε * N) + ((K * n : ℕ) : ℝ) * (K * (ε * N)) := hcard.trans (add_le_add hb1 hb2)
      _ = _ := by ring
  have h5 : (((K * n : ℕ) : ℝ) + 1) * K * ε * N < 1 * N := mul_lt_mul_of_pos_right h3 hN0
  linarith
end GeneralPieces.Group
