-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Parameters.exists_finite_cap_parameters
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:34:46.885073+00:00
-- url     : https://prove2.me/submissions/e6146c0c-7e8b-4f1e-98fa-246f153f4c1d

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Parameters
theorem h49_fl_ge (n : ℕ) (hn : 1 ≤ n) : 20 * n ≤ OAI.TreeEdit.BinaryLower.Parameters.finiteLength n := by
  unfold OAI.TreeEdit.BinaryLower.Parameters.finiteLength
  have h1 : 1 ≤ n ^ (20 * n) := Nat.one_le_pow _ _ hn
  have h2 : 20 * n ≤ 20 * n * n ^ (20 * n) := Nat.le_mul_of_pos_right _ h1
  have h3 : 20 * n * n ^ (20 * n) ≤ (20 * n * n ^ (20 * n)) ^ (3 * n) :=
    Nat.le_self_pow (by omega) _
  omega

theorem h49_bracket {k₀ d : ℕ} (hk₀ : 0 < k₀) (hd : finiteLength k₀ ≤ d) :
    ∃ k : ℕ, k₀ ≤ k ∧ finiteLength k ≤ d ∧ d < finiteLength (k + 1) := by
  have hex : ∃ m, k₀ ≤ m ∧ d < finiteLength m :=
    ⟨d + k₀ + 1, by omega, by have := h49_fl_ge (d + k₀ + 1) (by omega); omega⟩
  classical
  let m := Nat.find hex
  have hm : k₀ ≤ m ∧ d < finiteLength m := Nat.find_spec hex
  have hmk : m ≠ k₀ := by
    intro h; rw [h] at hm; omega
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · have := Nat.find_min hex (show m - 1 < m by omega)
    push_neg at this
    exact this (by omega)
  · have : m - 1 + 1 = m := by omega
    rw [this]; exact hm.2

theorem h49_fl_log {k : ℕ} (hk : 20 ≤ k) :
    Real.log (finiteLength (k + 1) : ℝ) ≤ 300 * (k : ℝ) ^ 2 * Real.log k := by
  have hk' : (20:ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (0:ℝ) < k + 1 := by linarith
  unfold finiteLength
  push_cast
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow]
  have hL : Real.log 20 ≤ Real.log k := Real.log_le_log (by norm_num) hk'
  have hL2 : Real.log ((k:ℝ)+1) ≤ 2 * Real.log k := by
    have : Real.log ((k:ℝ)+1) ≤ Real.log (2 * k) := Real.log_le_log hk1 (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    have : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hL0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hl1 : 0 ≤ Real.log ((k:ℝ)+1) := Real.log_nonneg (by linarith)
  push_cast
  have e1 : (3 * ((k:ℝ) + 1)) * (Real.log 20 + Real.log ((k:ℝ)+1) + (20 * ((k:ℝ)+1)) * Real.log ((k:ℝ)+1))
      ≤ (3 * ((k:ℝ) + 1)) * (Real.log k + 2 * Real.log k + (20 * ((k:ℝ)+1)) * (2 * Real.log k)) := by
    gcongr
  have e2 : (3 * ((k:ℝ) + 1)) * (Real.log k + 2 * Real.log k + (20 * ((k:ℝ)+1)) * (2 * Real.log k))
      = (3 * ((k:ℝ) + 1) * (40 * k + 43)) * Real.log k := by ring
  have e3 : 3 * ((k:ℝ) + 1) * (40 * k + 43) ≤ 300 * (k:ℝ)^2 := by nlinarith
  calc _ ≤ _ := e1
    _ = _ := e2
    _ ≤ 300 * (k:ℝ)^2 * Real.log k := mul_le_mul_of_nonneg_right e3 hL0
theorem h49_sqrt {k d : ℕ} (hk : 20 ≤ k) (hd : 2 ≤ d) (hcap : d ≤ finiteLength (k + 1)) :
    Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))) ≤ 40 * k * Real.log k := by
  have hk' : (20:ℝ) ≤ k := by exact_mod_cast hk
  have hL0 : 0 < Real.log k := Real.log_pos (by linarith)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = 300 * (k:ℝ)^2 * Real.log k := ⟨_, rfl⟩
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hld : Real.log d ≤ Λ := by
    have hc : (d:ℝ) ≤ (finiteLength (k+1) : ℝ) := Nat.cast_le.2 hcap
    have : Real.log (d:ℝ) ≤ Real.log (finiteLength (k+1) : ℝ) :=
      Real.log_le_log (by linarith) hc
    exact this.trans (hΛ ▸ h49_fl_log hk)
  clear hcap
  have hld0 : 0 < Real.log d := Real.log_pos (by linarith)
  have hLam : 0 < Λ := by rw [hΛ]; positivity
  -- log Λ ≤ 5 log k
  have hlogΛ : Real.log Λ ≤ 5 * Real.log k := by
    rw [hΛ, Real.log_mul (by positivity) hL0.ne', Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h300 : Real.log 300 ≤ 2 * Real.log k := by
      have : Real.log 300 ≤ Real.log ((k:ℝ)^2) := Real.log_le_log (by norm_num) (by nlinarith [hk'])
      rw [Real.log_pow] at this; push_cast at this; exact this
    have hll : Real.log (Real.log k) ≤ Real.log k := by
      have := Real.log_le_sub_one_of_pos hL0; linarith
    push_cast
    linarith
  have hprod : Real.log d * Real.log (Real.log d) ≤ (40 * k * Real.log k)^2 := by
    rcases le_or_gt (Real.log (Real.log d)) 0 with h | h
    · have : Real.log d * Real.log (Real.log d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hld0.le h
      nlinarith [sq_nonneg (40 * k * Real.log k)]
    · have h1 : Real.log (Real.log d) ≤ Real.log Λ := Real.log_le_log hld0 hld
      calc Real.log d * Real.log (Real.log d) ≤ Λ * Real.log Λ := by gcongr
        _ ≤ Λ * (5 * Real.log k) := by gcongr
        _ ≤ (40 * k * Real.log k)^2 := by rw [hΛ]; nlinarith [sq_nonneg (k * Real.log k)]
  calc Real.sqrt (Real.log d * Real.log (Real.log d)) ≤ Real.sqrt ((40 * k * Real.log k)^2) :=
        Real.sqrt_le_sqrt hprod
    _ = 40 * k * Real.log k := Real.sqrt_sq (by positivity)

theorem solution {c₀ : ℝ} (hc₀ : 0 < c₀) (K : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ k : ℕ,
      K ≤ k ∧ 20 ≤ k ∧ finiteLength k ≤ d ∧
        Real.exp ((1 / 160 : ℝ) *
          Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤
            c₀ * ((k : ℝ) / 4) ^ k := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = K + 60 + Nat.ceil |Real.log c₀| := ⟨_, rfl⟩
  refine ⟨finiteLength k₀, fun d hd => ?_⟩
  obtain ⟨k, hkk, hk1, hk2⟩ := h49_bracket (by omega) hd
  refine ⟨k, by omega, by omega, hk1, ?_⟩
  have hk20 : 20 ≤ k := by omega
  have hd2 : 2 ≤ d := by have := h49_fl_ge k₀ (by omega); omega
  have hs := h49_sqrt hk20 hd2 hk2.le
  have hkR : (60:ℝ) ≤ k := by exact_mod_cast (show 60 ≤ k by omega)
  have hcR : |Real.log c₀| ≤ k := by
    have : (Nat.ceil |Real.log c₀| : ℝ) ≤ k := by exact_mod_cast (show Nat.ceil |Real.log c₀| ≤ k by omega)
    exact (Nat.le_ceil _).trans this
  have hlogk : 4 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have he := Real.exp_one_lt_d9
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 : 0 < Real.exp 1 := Real.exp_pos 1
    have : Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
    linarith [show (2.7182818286:ℝ)^4 < 60 by norm_num]
  have hlog4 : Real.log 4 < 1.4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  have hlc : -Real.log c₀ ≤ k := by have := neg_abs_le (Real.log c₀); linarith
  have hkey : (1/160 : ℝ) * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))) ≤
      Real.log c₀ + k * (Real.log k - Real.log 4) := by
    have hX : (k:ℝ) * 4 ≤ k * Real.log k := mul_le_mul_of_nonneg_left hlogk (by linarith)
    have h4 : (k:ℝ) * Real.log 4 ≤ k * 1.4 := mul_le_mul_of_nonneg_left hlog4.le (by linarith)
    have e : (k:ℝ) * (Real.log k - Real.log 4) = k * Real.log k - k * Real.log 4 := by ring
    rw [e]
    have e2 : (40:ℝ) * k * Real.log k = 40 * (k * Real.log k) := by ring
    rw [e2] at hs
    linarith
  have hk0 : (0:ℝ) < k := by linarith
  have heq : ∀ (c x : ℝ) (n : ℕ), 0 < c → 0 < x →
      Real.exp (Real.log c + n * Real.log x) = c * x ^ n := by
    intro c x n hc hx
    rw [Real.exp_add, Real.exp_log hc, ← Real.log_pow, Real.exp_log (by positivity)]
  have hl4 : Real.log k - Real.log 4 = Real.log ((k:ℝ) / 4) := (Real.log_div hk0.ne' (by norm_num)).symm
  rw [hl4] at hkey
  have hpos4 : (0:ℝ) < (k:ℝ)/4 := div_pos hk0 (by norm_num)
  exact (Real.exp_le_exp.mpr hkey).trans_eq (heq c₀ ((k:ℝ)/4) k hc₀ hpos4)

