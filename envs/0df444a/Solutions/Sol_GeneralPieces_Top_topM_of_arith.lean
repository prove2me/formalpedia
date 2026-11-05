-- Prove2me | solution 1 for GeneralPieces.Top.topM_of_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:33:17.741116+00:00
-- url     : https://prove2.me/submissions/70c6041a-791e-4a0f-97a5-c1332d7e576b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_InOut
import Definitions.Def_GeneralPieces_Top_EndM
import Theorems.Thm_ClauseBound_Alg_End_eM_enc_le
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_ClauseBound_Alg_End_log_le_self
import Theorems.Thm_ClauseBound_Alg_End_mul_le_two_rpow
import Theorems.Thm_ClauseBound_Alg_End_n_le
import Theorems.Thm_ClauseBound_Alg_End_one_le_log
import Theorems.Thm_ClauseBound_Alg_End_one_le_mul_of_div_le
import Theorems.Thm_ClauseBound_Alg_End_time_le
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_n_le
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
attribute [local fun_prop] Groundwork.PolyT.length
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
open GeneralPieces GeneralPieces.Top
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat ClauseBound.Alg ClauseBound.Alg.End
namespace GeneralPieces.Top
theorem _root_.solution (hP : CountKSatRate.StPaddedW) (hC : StCorrectM) (hK : StCertM) {Idx : Type} [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ)
    (Q : S.Seq e C₀) (hA : ∃ A : ℕ, ∀ k m : ℕ, 1 ≤ k → S.K (Q.idx 0) ^ 9 ≤ m → (needTop S (Q.pick (root9 m)).2 k m : ℝ) ≤ A * k * m * e (Q.pick (root9 m)).1.length)
    (hS : S.Poly) (r : ℕ → ℝ) (c₁ : ℕ) (hr : ∀ m : ℕ, 1 ≤ m → 1 / (c₁ * Real.logb 2 ((m : ℝ) + 2) ^ c₁) ≤ r m)
    (he : ∀ m : ℕ, S.K (Q.idx 0) ^ 9 ≤ m → e (Q.pick (root9 m)).1.length ≤ c₁ * r m) : Tied.TopM S Q.pick r := by
  set K₀ := S.K (Q.idx 0) with hK₀
  obtain ⟨hAM, heM⟩ := hK Idx S hS Q.pick Q.pick_poly
  obtain ⟨N, q, hfin, hN⟩ := hP (eM S Q.pick) (AM S Q.pick) heM hAM
  obtain ⟨A, hA⟩ := hA
  -- c₁ ≥ 1, because e is positive
  have hc : 1 ≤ c₁ := by
    rcases Nat.eq_zero_or_pos c₁ with h0 | h0
    · exfalso
      have h1 := he (K₀ ^ 9) le_rfl
      have h2 := Q.e_ge (Q.pick (root9 (K₀ ^ 9))).1.length
      have h3 : (2 : ℝ) ≤ S.K (Q.idx (Q.pick (root9 (K₀ ^ 9))).1.length) := by exact_mod_cast Q.K_two _
      have h4 : 0 < Real.logb 2 (S.K (Q.idx (Q.pick (root9 (K₀ ^ 9))).1.length)) := Real.logb_pos (by norm_num) (by linarith)
      have h5 : 0 < 1 / Real.logb 2 (S.K (Q.idx (Q.pick (root9 (K₀ ^ 9))).1.length)) ^ C₀ := by positivity
      rw [h0] at h1
      simp only [Nat.cast_zero, zero_mul] at h1
      linarith
    · exact h0
  set H : ℕ := 2 * c₁ * (3 * (c₁ + 1).factorial * 2 ^ (c₁ + 1))
  set G : ℕ := A * c₁ + c₁ * (K₀ ^ 9 + 2) ^ c₁
  have hEall : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      (eM S Q.pick (SatM.enc k φ) : ℝ) ≤ (G : ℝ) * ((k : ℝ) * φ.length * r φ.length) := by
    intro k n φ hk hm hφ ho
    set m := φ.length with hmd
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hrm := hr m hm
    have hr0 : 0 ≤ r m := le_trans (by have := one_le_log m; positivity) hrm
    have hX : 0 ≤ (k : ℝ) * m * r m := by positivity
    have hn := n_le hφ ho
    obtain ⟨hEn, hEt⟩ := eM_enc_le hS Q.pick hk hφ.1
    have hGa : ((A * c₁ : ℕ) : ℝ) * ((k : ℝ) * m * r m) ≤ (G : ℝ) * ((k : ℝ) * m * r m) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right _ _) hX
    have hGb : ((c₁ * (K₀ ^ 9 + 2) ^ c₁ : ℕ) : ℝ) * ((k : ℝ) * m * r m) ≤ (G : ℝ) * ((k : ℝ) * m * r m) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left _ _) hX
    by_cases hs : m < K₀ ^ 9
    · refine le_trans ?_ hGb
      have h1 := one_le_mul_of_div_le hc (one_le_log m) hrm
      have h2 : Real.logb 2 ((m : ℝ) + 2) ≤ ((K₀ ^ 9 + 2 : ℕ) : ℝ) := by
        refine (log_le_self m).trans ?_
        have : m + 2 ≤ K₀ ^ 9 + 2 := by omega
        exact_mod_cast this
      have h3 : Real.logb 2 ((m : ℝ) + 2) ^ c₁ ≤ ((K₀ ^ 9 + 2 : ℕ) : ℝ) ^ c₁ := pow_le_pow_left₀ (by linarith [one_le_log m]) h2 _
      have h4 : 1 ≤ ((c₁ * (K₀ ^ 9 + 2) ^ c₁ : ℕ) : ℝ) * r m := by
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ hr0)
        rw [Nat.cast_mul, Nat.cast_pow]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      calc (eM S Q.pick (SatM.enc k φ) : ℝ) ≤ ((k * m : ℕ) : ℝ) := by exact_mod_cast hEn.trans hn
        _ = (k : ℝ) * m * 1 := by push_cast; ring
        _ ≤ (k : ℝ) * m * (((c₁ * (K₀ ^ 9 + 2) ^ c₁ : ℕ) : ℝ) * r m) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring
    · refine le_trans ?_ hGa
      have h1 := hA k m hk (not_lt.1 hs)
      have h2 := he m (not_lt.1 hs)
      calc (eM S Q.pick (SatM.enc k φ) : ℝ) ≤ (needTop S (Q.pick (root9 m)).2 k m : ℝ) := by exact_mod_cast hEt
        _ ≤ A * k * m * e (Q.pick (root9 m)).1.length := h1
        _ ≤ A * k * m * (c₁ * r m) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by push_cast; ring
  refine ⟨hAM, heM, fun k n φ hk hm hφ ho pad hpad => hC Idx S e C₀ Q hS k n φ hk hm hφ ho pad hpad, ⟨G, hEall⟩,
    N, q, q * 9 ^ q + q * (2 * H + G), hfin, hN, fun k n φ hk hm hφ ho => ?_⟩
  have hE := hEall k n φ hk hm hφ ho
  set m := φ.length with hmd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrm := hr m hm
  have hr0 : 0 ≤ r m := le_trans (by have := one_le_log m; positivity) hrm
  have hX : 0 ≤ (k : ℝ) * m * r m := by positivity
  have hn := n_le hφ ho
  have hx := hN (SatM.enc k φ)
  rw [hC Idx S e C₀ Q hS k n φ hk hm hφ ho (pad (eM S Q.pick (SatM.enc k φ))) (by simp [pad])] at hx
  obtain ⟨ev⟩ := hx
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  unfold SatM.bound
  refine Nat.le_floor ?_
  have ht := time_le q (SatM.enc k φ).length (eM S Q.pick (SatM.enc k φ)) (k * m) H G hX (Nat.mul_pos hk hm)
    (length_enc_succ_le hk hm hn) (mul_le_two_rpow hc hk hm hrm) hE
  refine ht.trans (le_of_eq ?_)
  congr 2
  ring
end GeneralPieces.Top
