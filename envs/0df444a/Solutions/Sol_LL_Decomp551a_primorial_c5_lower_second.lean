-- Prove2me | solution 1 for LL_Decomp551a.primorial_c5_lower_second
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:35:26.432629+00:00
-- url     : https://prove2.me/submissions/8949898e-042c-4e11-8bf2-549012f10ab4

import Mathlib
import Definitions.Def_ThetaCertCore
import Definitions.Def_PrimorialCertData_0
import Theorems.Thm_PrimorialCert_block_0
import Definitions.Def_PrimorialCertData_1
import Theorems.Thm_PrimorialCert_block_1
import Definitions.Def_PrimorialCertData_2
import Theorems.Thm_PrimorialCert_block_2
import Definitions.Def_PrimorialCertData_3
import Theorems.Thm_PrimorialCert_block_3
import Definitions.Def_PrimorialCertData_4
import Theorems.Thm_PrimorialCert_block_4
import Definitions.Def_PrimorialCertData_5
import Theorems.Thm_PrimorialCert_block_5
import Definitions.Def_PrimorialCertData_6
import Theorems.Thm_PrimorialCert_block_6
import Definitions.Def_PrimorialCertData_7
import Theorems.Thm_PrimorialCert_block_7
import Definitions.Def_PrimorialCertData_8
import Theorems.Thm_PrimorialCert_block_8
import Definitions.Def_PrimorialCertData_9
import Theorems.Thm_PrimorialCert_block_9
import Definitions.Def_PrimorialCertData_10
import Theorems.Thm_PrimorialCert_block_10
import Definitions.Def_PrimorialCertData_11
import Theorems.Thm_PrimorialCert_block_11
import Definitions.Def_PrimorialCertData_12
import Theorems.Thm_PrimorialCert_block_12
import Definitions.Def_PrimorialCertData_13
import Theorems.Thm_PrimorialCert_block_13
import Definitions.Def_PrimorialCertData_14
import Theorems.Thm_PrimorialCert_block_14
import Definitions.Def_PrimorialCertData_15
import Theorems.Thm_PrimorialCert_block_15
import Definitions.Def_PrimorialCertData_16
import Theorems.Thm_PrimorialCert_block_16
import Definitions.Def_PrimorialCertData_17
import Theorems.Thm_PrimorialCert_block_17
import Definitions.Def_PrimorialCertData_18
import Theorems.Thm_PrimorialCert_block_18
import Definitions.Def_PrimorialCertData_19
import Theorems.Thm_PrimorialCert_block_19
import Definitions.Def_PrimorialCertData_20
import Theorems.Thm_PrimorialCert_block_20
import Definitions.Def_PrimorialCertData_21
import Theorems.Thm_PrimorialCert_block_21
import Definitions.Def_PrimorialCertData_22
import Theorems.Thm_PrimorialCert_block_22
import Definitions.Def_PrimorialCertData_23
import Theorems.Thm_PrimorialCert_block_23
import Definitions.Def_PrimorialCertData_24
import Theorems.Thm_PrimorialCert_block_24
import Definitions.Def_PrimorialCertData_25
import Theorems.Thm_PrimorialCert_block_25
import Definitions.Def_PrimorialCertData_26
import Theorems.Thm_PrimorialCert_block_26
import Definitions.Def_PrimorialCertData_27
import Theorems.Thm_PrimorialCert_block_27
import Definitions.Def_PrimorialCertData_28
import Theorems.Thm_PrimorialCert_block_28
import Definitions.Def_PrimorialCertData_29
import Theorems.Thm_PrimorialCert_block_29
import Definitions.Def_PrimorialCertData_30
import Theorems.Thm_PrimorialCert_block_30
import Definitions.Def_PrimorialCertData_31
import Theorems.Thm_PrimorialCert_block_31
import Definitions.Def_PrimorialCertData_32
import Theorems.Thm_PrimorialCert_block_32
import Definitions.Def_PrimorialCertData_33
import Theorems.Thm_PrimorialCert_block_33
import Definitions.Def_PrimorialCertData_34
import Theorems.Thm_PrimorialCert_block_34
import Definitions.Def_PrimorialCertData_35
import Theorems.Thm_PrimorialCert_block_35
import Definitions.Def_PrimorialCertData_36
import Theorems.Thm_PrimorialCert_block_36
import Definitions.Def_PrimorialCertData_37
import Theorems.Thm_PrimorialCert_block_37
import Definitions.Def_PrimorialCertData_38
import Theorems.Thm_PrimorialCert_block_38
import Definitions.Def_PrimorialCertData_39
import Theorems.Thm_PrimorialCert_block_39
import Definitions.Def_PrimorialCertData_40
import Theorems.Thm_PrimorialCert_block_40
import Definitions.Def_PrimorialCertData_41
import Theorems.Thm_PrimorialCert_block_41
import Definitions.Def_PrimorialCertData_42
import Theorems.Thm_PrimorialCert_block_42
import Definitions.Def_PrimorialCertData_43
import Theorems.Thm_PrimorialCert_block_43
import Definitions.Def_PrimorialCertData_44
import Theorems.Thm_PrimorialCert_block_44
import Definitions.Def_PrimorialCertData_45
import Theorems.Thm_PrimorialCert_block_45
import Definitions.Def_PrimorialCertData_46
import Theorems.Thm_PrimorialCert_block_46
import Definitions.Def_PrimorialCertData_47
import Theorems.Thm_PrimorialCert_block_47
import Definitions.Def_PrimorialCertData_48
import Theorems.Thm_PrimorialCert_block_48
import Definitions.Def_PrimorialCertData_49
import Theorems.Thm_PrimorialCert_block_49
import Definitions.Def_PrimorialCertData_50
import Theorems.Thm_PrimorialCert_block_50
import Definitions.Def_PrimorialCertData_51
import Theorems.Thm_PrimorialCert_block_51
import Definitions.Def_PrimorialCertData_52
import Theorems.Thm_PrimorialCert_block_52
import Definitions.Def_PrimorialCertData_53
import Theorems.Thm_PrimorialCert_block_53
import Definitions.Def_PrimorialCertData_54
import Theorems.Thm_PrimorialCert_block_54
import Definitions.Def_PrimorialCertData_55
import Theorems.Thm_PrimorialCert_block_55
import Definitions.Def_PrimorialCertData_56
import Theorems.Thm_PrimorialCert_block_56
import Definitions.Def_PrimorialCertData_57
import Theorems.Thm_PrimorialCert_block_57
import Definitions.Def_PrimorialCertData_58
import Theorems.Thm_PrimorialCert_block_58
import Definitions.Def_PrimorialCertData_59
import Theorems.Thm_PrimorialCert_block_59
import Definitions.Def_PrimorialCertData_60
import Theorems.Thm_PrimorialCert_block_60
import Definitions.Def_PrimorialCertData_61
import Theorems.Thm_PrimorialCert_block_61
import Definitions.Def_PrimorialCertData_62
import Theorems.Thm_PrimorialCert_block_62
import Definitions.Def_PrimorialCertData_63
import Theorems.Thm_PrimorialCert_block_63
import Definitions.Def_PrimorialCertData_64
import Theorems.Thm_PrimorialCert_block_64
import Definitions.Def_PrimorialCertData_65
import Theorems.Thm_PrimorialCert_block_65
import Definitions.Def_PrimorialCertData_66
import Theorems.Thm_PrimorialCert_block_66
import Definitions.Def_PrimorialCertData_67
import Theorems.Thm_PrimorialCert_block_67
import Definitions.Def_PrimorialCertData_68
import Theorems.Thm_PrimorialCert_block_68
import Definitions.Def_PrimorialCertData_69
import Theorems.Thm_PrimorialCert_block_69
import Definitions.Def_PrimorialCertData_70
import Theorems.Thm_PrimorialCert_block_70
import Definitions.Def_PrimorialCertData_71
import Theorems.Thm_PrimorialCert_block_71
import Definitions.Def_PrimorialCertData_72
import Theorems.Thm_PrimorialCert_block_72
import Definitions.Def_PrimorialCertData_73
import Theorems.Thm_PrimorialCert_block_73
import Definitions.Def_PrimorialCertData_74
import Theorems.Thm_PrimorialCert_block_74


set_option autoImplicit false

-- ===== inlined from dusartcert/LogSound =====

open Finset

set_option autoImplicit false

namespace DusartCert

/-- The atanh series for `log y`, `y ≥ 1`. -/
lemma hasSum_log_atanh {y : ℝ} (hy : 1 ≤ y) :
    HasSum (fun j : ℕ => 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1)) (Real.log y) := by
  have hz0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  have hz1 : (y - 1) / (y + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := (y - 1) / (y + 1)) (by rw [abs_of_nonneg hz0]; exact hz1)
  convert h using 1
  rw [← Real.log_div (by positivity) (by linarith)]
  congr 1
  field_simp; ring

lemma atanh_lower {y : ℝ} (hy : 1 ≤ y) (K : ℕ) :
    ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1) ≤ Real.log y := by
  have hz0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  exact sum_le_hasSum _ (fun j _ => by positivity) (hasSum_log_atanh hy)

lemma atanh_upper {y : ℝ} (hy : 1 ≤ y) (K : ℕ) :
    Real.log y ≤ ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1) +
      2 * ((y - 1) / (y + 1)) ^ (2 * K + 1) / ((2 * K + 1) * (1 - ((y - 1) / (y + 1)) ^ 2)) := by
  set z := (y - 1) / (y + 1) with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  have hS := hasSum_log_atanh hy
  rw [← hz] at hS
  have hsplit := hS.summable.sum_add_tsum_nat_add K
  rw [hS.tsum_eq] at hsplit
  rw [← hsplit]
  gcongr
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hgeo : Summable fun j : ℕ => 2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j :=
    (summable_geometric_of_lt_one (by positivity) hz2).mul_left _
  have hle : ∀ j : ℕ, 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * z ^ (2 * (j + K) + 1) ≤
      2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j := by
    intro j
    rw [← pow_mul, show 2 * (j + K) + 1 = (2 * K + 1) + 2 * j by ring, pow_add]
    have h1 : 1 / (2 * ((j + K : ℕ) : ℝ) + 1) ≤ 1 / (2 * (K : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); push_cast; linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
    have h2 : 0 ≤ z ^ (2 * K + 1) * z ^ (2 * j) := by positivity
    calc 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * (z ^ (2 * K + 1) * z ^ (2 * j))
        ≤ 2 * (1 / (2 * (K : ℝ) + 1)) * (z ^ (2 * K + 1) * z ^ (2 * j)) := by gcongr
      _ = 2 * z ^ (2 * K + 1) / (2 * K + 1) * z ^ (2 * j) := by ring
  calc ∑' j : ℕ, 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * z ^ (2 * (j + K) + 1)
      ≤ ∑' j : ℕ, 2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j :=
        Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun j => by positivity) hle) hgeo
    _ = 2 * z ^ (2 * K + 1) / ((2 * K + 1) * (1 - z ^ 2)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hz2]
        have : (1 - z ^ 2) ≠ 0 := by linarith
        field_simp

lemma floor_div_le (N D : ℕ) (hD : 0 < D) : ((N / D : ℕ) : ℝ) ≤ (N : ℝ) / D := by
  rw [le_div_iff₀ (by exact_mod_cast hD)]; exact_mod_cast Nat.div_mul_le_self N D

lemma le_cdiv (N D : ℕ) (hD : 0 < D) : (N : ℝ) / D ≤ (cdiv N D : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hD)]
  have h2 := Nat.div_add_mod (N + D - 1) D
  have h3 := Nat.mod_lt (N + D - 1) hD
  have : N ≤ cdiv N D * D := by
    unfold cdiv; rw [Nat.mul_comm] at h2
    generalize (N + D - 1) / D * D = X at *; omega
  exact_mod_cast this

/-- The real term `Q · 2 (a/b)^(2j+1)/(2j+1)`. -/
lemma lterm_real (Q a b j : ℕ) (hb : 0 < b) :
    (Q : ℝ) * (2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1)) =
      ((2 * Q * a ^ (2 * j + 1) : ℕ) : ℝ) / (((2 * j + 1) * b ^ (2 * j + 1) : ℕ) : ℝ) := by
  have : (b : ℝ) ≠ 0 := by positivity
  push_cast; rw [div_pow]; field_simp

lemma lsumLo_le (Q a b : ℕ) (hb : 0 < b) : ∀ K, (lsumLo Q a b K : ℝ) ≤
    (Q : ℝ) * ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) := by
  intro K; induction K with
  | zero => simp [lsumLo]
  | succ K ih =>
    rw [lsumLo, Nat.cast_add, sum_range_succ, mul_add, lterm_real Q a b K hb]
    have := floor_div_le (2 * Q * a ^ (2 * K + 1)) ((2 * K + 1) * b ^ (2 * K + 1)) (by positivity)
    unfold ltermLo; linarith

lemma lsumHi_ge (Q a b : ℕ) (hb : 0 < b) : ∀ K,
    (Q : ℝ) * ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) ≤ (lsumHi Q a b K : ℝ) := by
  intro K; induction K with
  | zero => simp [lsumHi]
  | succ K ih =>
    rw [lsumHi, Nat.cast_add, sum_range_succ, mul_add, lterm_real Q a b K hb]
    have := le_cdiv (2 * Q * a ^ (2 * K + 1)) ((2 * K + 1) * b ^ (2 * K + 1)) (by positivity)
    unfold ltermHi; linarith

/-- **Reduced log bounds.** For `0 < den ≤ num`: `logRedLo ≤ Q log(num/den) ≤ logRedHi`. -/
theorem logRed_bounds (Q num den : ℕ) (hd : 0 < den) (hle : den ≤ num) :
    (logRedLo Q num den : ℝ) ≤ Q * Real.log ((num : ℝ) / den) ∧
      Q * Real.log ((num : ℝ) / den) ≤ (logRedHi Q num den : ℝ) := by
  have hden : (0 : ℝ) < den := by exact_mod_cast hd
  have hy : (1 : ℝ) ≤ (num : ℝ) / den := by rw [le_div_iff₀ hden]; simp; exact_mod_cast hle
  have hb : 0 < num + den := by omega
  have hz : ((num : ℝ) / den - 1) / ((num : ℝ) / den + 1) = (((num - den : ℕ) : ℝ)) / ((num + den : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast; field_simp
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  constructor
  · have := atanh_lower hy nterms
    rw [hz] at this
    exact (lsumLo_le Q (num - den) (num + den) hb nterms).trans (mul_le_mul_of_nonneg_left this hQ)
  · have hu := atanh_upper hy nterms
    rw [hz] at hu
    have h1 := lsumHi_ge Q (num - den) (num + den) hb nterms
    -- remainder
    set a := num - den; set b := num + den
    have hab : a < b := by omega
    have hb2 : 0 < b ^ 2 - a ^ 2 := by
      have : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
      omega
    have hrem := le_cdiv (2 * Q * a ^ (2 * nterms + 1) * b ^ 2) ((2 * nterms + 1) * b ^ (2 * nterms + 1) * (b ^ 2 - a ^ 2))
      (by positivity)
    have hremeq : (Q : ℝ) * (2 * ((a : ℝ) / b) ^ (2 * nterms + 1) / ((2 * nterms + 1) * (1 - ((a : ℝ) / b) ^ 2))) =
        ((2 * Q * a ^ (2 * nterms + 1) * b ^ 2 : ℕ) : ℝ) /
          (((2 * nterms + 1) * b ^ (2 * nterms + 1) * (b ^ 2 - a ^ 2) : ℕ) : ℝ) := by
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have hsub : ((b ^ 2 - a ^ 2 : ℕ) : ℝ) = (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hne : (b : ℝ) ^ 2 - (a : ℝ) ^ 2 ≠ 0 := by
        rw [← hsub]; exact_mod_cast hb2.ne'
      push_cast [hsub]
      simp only [div_pow]
      field_simp
    unfold logRedHi lrem
    rw [Nat.cast_add]
    calc (Q : ℝ) * Real.log ((num : ℝ) / den) ≤ (Q : ℝ) * (∑ j ∈ range nterms,
          2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) +
          2 * ((a : ℝ) / b) ^ (2 * nterms + 1) / ((2 * nterms + 1) * (1 - ((a : ℝ) / b) ^ 2))) :=
          mul_le_mul_of_nonneg_left hu hQ
      _ ≤ _ := by rw [mul_add, hremeq]; linarith

/-- **Log bounds with range reduction.** -/
theorem log_bounds (Q num den k : ℕ) (h : redOK num den k = true) :
    (logLo Q num den k : ℝ) ≤ Q * Real.log ((num : ℝ) / den) ∧
      Q * Real.log ((num : ℝ) / den) ≤ (logHi Q num den k : ℝ) := by
  simp only [redOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, _⟩, hd⟩ := h
  have h2 := logRed_bounds Q 2 1 one_pos (by norm_num)
  have hk := logRed_bounds Q num (den * 2 ^ k) (by positivity) h1
  have hden : (0 : ℝ) < den := by exact_mod_cast hd
  have hsplit : Real.log ((num : ℝ) / den) = k * Real.log 2 + Real.log ((num : ℝ) / ((den * 2 ^ k : ℕ) : ℝ)) := by
    have hnum : (0 : ℝ) < num := by
      have : 0 < den * 2 ^ k := by positivity
      exact_mod_cast lt_of_lt_of_le this h1
    push_cast
    rw [Real.log_div hnum.ne' hden.ne', Real.log_div hnum.ne' (by positivity : (den : ℝ) * 2 ^ k ≠ 0),
      Real.log_mul hden.ne' (by positivity), Real.log_pow]; ring
  have hl2 : Real.log ((2 : ℕ) / ((1 : ℕ) : ℝ)) = Real.log 2 := by norm_num
  rw [hl2] at h2
  unfold logLo logHi
  push_cast
  rw [hsplit]
  constructor
  · nlinarith [h2.1, hk.1, show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  · nlinarith [h2.2, hk.2, show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

end DusartCert
-- ===== inlined from thetasieve/PopSound =====

/-! Soundness of the SWAR popcount `ThetaSieve.popcountW`: for `x < 2^W` it equals the number of set bits of `x`. -/

set_option autoImplicit false

namespace ThetaSieve

/-- Horner encoding of `n` fields of width `f`: `c 0 + 2^f (c 1 + 2^f (…))`. -/
def encF (f : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, c => c 0 + 2 ^ f * encF f n (fun j => c (j + 1))

lemma encF_testBit {f : ℕ} (hf : 0 < f) : ∀ (n : ℕ) (c : ℕ → ℕ), (∀ j, c j < 2 ^ f) → ∀ i,
    (encF f n c).testBit i = (decide (i / f < n) && (c (i / f)).testBit (i % f)) := by
  intro n
  induction n with
  | zero => intro c _ i; simp [encF]
  | succ n ih =>
    intro c hc i
    rw [encF, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (hc 0)]
    split_ifs with h
    · have h1 : i / f = 0 := Nat.div_eq_of_lt h
      have h2 : i % f = i := Nat.mod_eq_of_lt h
      simp [h1, h2]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
      rw [ih _ (fun j => hc (j + 1)), Nat.add_sub_cancel_left, Nat.add_div_left _ hf, Nat.add_mod_left]
      simp

lemma encF_zero_fun (f : ℕ) : ∀ (n : ℕ) (c : ℕ → ℕ), (∀ j, c j = 0) → encF f n c = 0 := by
  intro n; induction n with
  | zero => intro c _; rfl
  | succ n ih => intro c hc; rw [encF, hc 0, ih _ (fun j => hc (j + 1))]; simp

lemma encF_pad (f : ℕ) : ∀ (n k : ℕ) (c : ℕ → ℕ), (∀ j, n ≤ j → c j = 0) → encF f (n + k) c = encF f n c := by
  intro n; induction n with
  | zero => intro k c hc; simp only [Nat.zero_add]; rw [encF_zero_fun f k c (fun j => hc j (Nat.zero_le _))]; rfl
  | succ n ih =>
    intro k c hc
    rw [show n + 1 + k = (n + k) + 1 by ring, encF, encF, ih k _ (fun j hj => hc (j + 1) (by omega))]

lemma encF_pad_eq {g W : ℕ} {c : ℕ → ℕ} (hc : ∀ j, W ≤ j * g → c j = 0) {n m : ℕ} (hn : W ≤ n * g) (hm : W ≤ m * g) :
    encF g n c = encF g m c := by
  have hn0 : W ≤ min n m * g := by
    rcases le_total n m with h | h
    · rw [min_eq_left h]; exact hn
    · rw [min_eq_right h]; exact hm
  have hz : ∀ j, min n m ≤ j → c j = 0 := fun j hj => hc j (le_trans hn0 (Nat.mul_le_mul_right g hj))
  calc encF g n c = encF g (min n m + (n - min n m)) c := by congr 1; omega
    _ = encF g (min n m) c := encF_pad g _ _ c hz
    _ = encF g (min n m + (m - min n m)) c := (encF_pad g _ _ c hz).symm
    _ = encF g m c := by congr 1; omega

lemma encF_add (f : ℕ) : ∀ (n : ℕ) (a b : ℕ → ℕ), encF f n a + encF f n b = encF f n (fun j => a j + b j) := by
  intro n; induction n with
  | zero => intro a b; rfl
  | succ n ih => intro a b; simp only [encF]; rw [← ih]; ring

lemma encF_mul (f : ℕ) : ∀ (n : ℕ) (a : ℕ → ℕ) (d : ℕ), encF f n a * d = encF f n (fun j => a j * d) := by
  intro n; induction n with
  | zero => intro a d; simp [encF]
  | succ n ih => intro a d; simp only [encF]; rw [← ih]; ring

lemma encF_regroup (f : ℕ) : ∀ (n : ℕ) (c : ℕ → ℕ),
    encF f (2 * n) c = encF (2 * f) n (fun j => c (2 * j) + 2 ^ f * c (2 * j + 1)) := by
  intro n; induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, encF, encF, ih, encF]
    have e : (fun j => c (j + 1 + 1)) = (fun j => c (j + 2)) := rfl
    have e2 : (fun j => c (2 * j + 2) + 2 ^ f * c (2 * j + 1 + 2)) =
        (fun j => c (2 * (j + 1)) + 2 ^ f * c (2 * (j + 1) + 1)) := by
      funext j; rw [show 2 * j + 2 = 2 * (j + 1) by ring, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring]
    simp only [e, e2, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    rw [two_mul f, pow_add]; ring

lemma encF_and {f : ℕ} (hf : 0 < f) (n : ℕ) (a b : ℕ → ℕ) (ha : ∀ j, a j < 2 ^ f) (hb : ∀ j, b j < 2 ^ f) :
    encF f n a &&& encF f n b = encF f n (fun j => a j &&& b j) := by
  have hab : ∀ j, (a j &&& b j) < 2 ^ f := fun j => lt_of_le_of_lt Nat.and_le_left (ha j)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, encF_testBit hf n a ha, encF_testBit hf n b hb, encF_testBit hf n _ hab, Nat.testBit_and]
  cases decide (i / f < n) <;> simp

lemma encF_shift (f : ℕ) (n : ℕ) (c : ℕ → ℕ) (h0 : c 0 < 2 ^ f) :
    encF f (n + 1) c >>> f = encF f n (fun j => c (j + 1)) := by
  rw [Nat.shiftRight_eq_div_pow, encF, Nat.add_mul_div_left _ _ (Nat.two_pow_pos f), Nat.div_eq_of_lt h0, Nat.zero_add]

lemma geom_eq_encF {p : ℕ} (hp : 1 ≤ p) (n : ℕ) : geom p n = encF p n (fun _ => 1) := by
  have key : ∀ n, encF p n (fun _ => 1) * (2 ^ p - 1) + 1 = 2 ^ (p * n) := by
    intro n; induction n with
    | zero => simp [encF]
    | succ n ih =>
      have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
      simp only [encF] at ih ⊢
      rw [Nat.mul_succ, pow_add]
      zify [h1] at ih ⊢
      push_cast at ih ⊢
      nlinarith [ih]
  have h2 : 0 < 2 ^ p - 1 := by
    have : 2 ≤ 2 ^ p := by calc 2 = 2 ^ 1 := by norm_num
                             _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    omega
  unfold geom
  rw [← key n, Nat.add_sub_cancel, Nat.mul_div_cancel _ h2]

/-- Number of set bits of `x` below `W` in the block `[j f, (j+1) f)`. -/
def cnt (x W f j : ℕ) : ℕ := ((Finset.Ico (j * f) ((j + 1) * f)).filter (fun i => i < W ∧ x.testBit i = true)).card

lemma cnt_le (x W f j : ℕ) : cnt x W f j ≤ f := by
  unfold cnt
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Nat.card_Ico]; ring_nf; omega

lemma cnt_lt {x W f j : ℕ} (hf : 0 < f) : cnt x W f j < 2 ^ f := lt_of_le_of_lt (cnt_le x W f j) (Nat.lt_two_pow_self)

lemma cnt_zero_of {x W f j : ℕ} (h : W ≤ j * f) : cnt x W f j = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi; simp only [Finset.mem_Ico] at hi; omega

lemma cnt_split (x W f j : ℕ) : cnt x W (2 * f) j = cnt x W f (2 * j) + cnt x W f (2 * j + 1) := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (by nlinarith) (by nlinarith)]
    congr 1; ring_nf
  · rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ico] at h1 h2; nlinarith [h1.1.2, h2.1.1]

/-- One SWAR round. -/
lemma round_eq {x W k : ℕ} :
    (encF (2 ^ k) (2 * (W / (2 * 2 ^ k) + 1)) (cnt x W (2 ^ k)) &&& swarMask W k) +
      ((encF (2 ^ k) (2 * (W / (2 * 2 ^ k) + 1)) (cnt x W (2 ^ k)) >>> 2 ^ k) &&& swarMask W k) =
      encF (2 * 2 ^ k) (W / (2 * 2 ^ k) + 1) (cnt x W (2 * 2 ^ k)) := by
  unfold swarMask
  have hf : 0 < 2 ^ k := Nat.two_pow_pos k
  generalize 2 ^ k = f at hf ⊢
  have hW : W < (W / (2 * f) + 1) * (2 * f) := by
    rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add (by omega)
  generalize W / (2 * f) + 1 = N at hW ⊢
  -- the mask as width-f fields
  set alt : ℕ → ℕ := fun j => if j % 2 = 0 then 2 ^ f - 1 else 0 with halt_def
  have halt : ∀ j, alt j < 2 ^ f := fun j => by
    simp only [alt]; have := Nat.two_pow_pos f; split_ifs <;> omega
  have hM : geom (2 * f) N * (2 ^ f - 1) = encF f (2 * N) alt := by
    rw [encF_regroup, geom_eq_encF (by omega), encF_mul]
    congr 1; funext j
    simp only [alt, Nat.mul_mod_right, if_true, show (2 * j + 1) % 2 = 1 by omega, one_ne_zero, if_false,
      mul_zero, add_zero, one_mul]
  have hc : ∀ j, cnt x W f j < 2 ^ f := fun j => cnt_lt hf
  have hE : encF f (2 * N) (cnt x W f) &&& encF f (2 * N) alt = encF (2 * f) N (fun j => cnt x W f (2 * j)) := by
    rw [encF_and hf _ _ _ hc halt, encF_regroup]
    congr 1; funext j
    simp only [alt, Nat.mul_mod_right, if_true, show (2 * j + 1) % 2 = 1 by omega, one_ne_zero, if_false,
      Nat.and_zero, mul_zero, add_zero, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hc _)]
  have hsh : encF f (2 * N) (cnt x W f) >>> f = encF f (2 * N) (fun j => cnt x W f (j + 1)) := by
    have h2N : 2 * N = (2 * N - 1) + 1 := by
      rcases Nat.eq_zero_or_pos N with rfl | h
      · simp at hW
      · omega
    rw [h2N, encF_shift _ _ _ (hc 0)]
    refine (encF_pad f _ 1 _ (fun j hj => cnt_zero_of ?_)).symm
    have h1 : 2 * N * f ≤ (j + 1) * f := Nat.mul_le_mul_right f (by omega)
    have h2 : N * (2 * f) = 2 * N * f := by ring
    omega
  have hO : encF f (2 * N) (fun j => cnt x W f (j + 1)) &&& encF f (2 * N) alt =
      encF (2 * f) N (fun j => cnt x W f (2 * j + 1)) := by
    rw [encF_and hf _ _ _ (fun j => hc _) halt, encF_regroup]
    congr 1; funext j
    simp only [alt, Nat.mul_mod_right, if_true, show (2 * j + 1) % 2 = 1 by omega, one_ne_zero, if_false,
      Nat.and_zero, mul_zero, add_zero, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hc _)]
  rw [hM, hE, hsh, hO, encF_add]
  congr 1; funext j; rw [cnt_split]

/-- The invariant after `k` rounds. -/
lemma pcAux_eq {x W : ℕ} : ∀ (fuel k : ℕ),
    pcAux W fuel k (encF (2 ^ k) (2 * (W / (2 * 2 ^ k) + 1)) (cnt x W (2 ^ k))) =
      encF (2 ^ (k + fuel)) (2 * (W / (2 * 2 ^ (k + fuel)) + 1)) (cnt x W (2 ^ (k + fuel))) := by
  intro fuel
  induction fuel with
  | zero => intro k; rfl
  | succ fuel ih =>
    intro k
    rw [pcAux, round_eq, show k + (fuel + 1) = (k + 1) + fuel by ring, ← ih (k + 1)]
    congr 1
    rw [pow_succ, mul_comm (2 ^ k) 2]
    have hf : 0 < 2 * 2 ^ k := by positivity
    apply encF_pad_eq (g := 2 * 2 ^ k) (W := W) (fun j hj => cnt_zero_of hj)
    · have := Nat.lt_div_mul_add (a := W) (b := 2 * 2 ^ k) hf; nlinarith
    · have := Nat.lt_div_mul_add (a := W) (b := 2 * (2 * 2 ^ k)) (by positivity); nlinarith

/-- **Soundness of the SWAR popcount.** -/
theorem popcountW_eq {W x : ℕ} (hx : x < 2 ^ W) :
    popcountW W x = ((Finset.range W).filter (fun i => x.testBit i = true)).card := by
  -- base: x as width-1 fields
  have hbase : x = encF (2 ^ 0) (2 * (W / (2 * 2 ^ 0) + 1)) (cnt x W (2 ^ 0)) := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [encF_testBit (by norm_num) _ _ (fun j => cnt_lt (by norm_num))]
    simp only [pow_zero, Nat.div_one, Nat.mod_one]
    by_cases hi : i < W
    · have hcnt : cnt x W 1 i = if x.testBit i = true then 1 else 0 := by
        unfold cnt
        rw [show Finset.Ico (i * 1) ((i + 1) * 1) = {i} by ext; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega,
          Finset.filter_singleton]
        by_cases hb : x.testBit i = true <;> simp [hb, hi]
      rw [hcnt]
      have : i < 2 * (W / 2 + 1) := by omega
      by_cases hb : x.testBit i = true <;> simp [hb, this]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi))),
        cnt_zero_of (by simpa using not_lt.1 hi)]
      simp
  unfold popcountW
  nth_rewrite 1 [hbase]
  rw [pcAux_eq, Nat.zero_add]
  set K := Nat.log2 W + 1
  have hK : W < 2 ^ K := Nat.lt_log2_self
  rw [encF_pad_eq (g := 2 ^ K) (W := W) (fun j hj => cnt_zero_of hj) (m := 1)
    (by have := Nat.lt_div_mul_add (a := W) (b := 2 * 2 ^ K) (by positivity); nlinarith) (by simpa using hK.le)]
  simp only [encF, mul_zero, add_zero]
  unfold cnt
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨Nat.zero_le _, by omega⟩, h1, h2⟩

end ThetaSieve
-- ===== inlined from thetasieve/MaskSound =====

/-! Soundness of the prime-multiple mask `ThetaSieve.pmask`: bit `i` is set exactly when `i < W` and
`L + 2 i` is a multiple of `p` that is at least `p * p`. -/

set_option autoImplicit false

namespace ThetaSieve

/-- The first odd multiple of `p` that is at least `max (p * p) L` (as computed inside `pmask`). -/
def fm (L p : ℕ) : ℕ :=
  let m0 := max (p * p) (((L + p - 1) / p) * p)
  if m0 % 2 == 0 then m0 + p else m0

lemma pmask_eq (L W p : ℕ) : pmask L W p =
    if L + 2 * W ≤ fm L p then 0 else geom p ((W - 1 - (fm L p - L) / 2) / p + 1) <<< ((fm L p - L) / 2) := rfl

lemma fm_spec {L p : ℕ} (hL : L % 2 = 1) (hp : p % 2 = 1) :
    fm L p % 2 = 1 ∧ p ∣ fm L p ∧ L ≤ fm L p ∧ p * p ≤ fm L p ∧
      ∀ n, n % 2 = 1 → p ∣ n → L ≤ n → p * p ≤ n → fm L p ≤ n := by
  have hp0 : 0 < p := by omega
  set c := (L + p - 1) / p with hc
  have hcL : L ≤ c * p := by
    have := Nat.lt_div_mul_add (a := L + p - 1) hp0; rw [← hc] at this; omega
  have hcmin : ∀ q, L ≤ q * p → c ≤ q := by
    intro q hq
    have : c < q + 1 := (Nat.div_lt_iff_lt_mul hp0).2 (by rw [Nat.add_mul, Nat.one_mul]; omega)
    omega
  have hm0d : p ∣ max (p * p) (c * p) := by
    rcases le_total (p * p) (c * p) with h | h
    · rw [max_eq_right h]; exact Dvd.intro_left c rfl
    · rw [max_eq_left h]; exact Dvd.intro p rfl
  have hm0min : ∀ n, p ∣ n → L ≤ n → p * p ≤ n → max (p * p) (c * p) ≤ n := by
    rintro n ⟨q, rfl⟩ h1 h2
    exact max_le h2 (by rw [mul_comm p q]; exact Nat.mul_le_mul_right p (hcmin q (by rw [mul_comm]; exact h1)))
  unfold fm
  simp only [← hc]
  generalize hm0 : max (p * p) (c * p) = m0 at hm0d hm0min
  have hm0p : p * p ≤ m0 := hm0 ▸ le_max_left _ _
  have hm0L : L ≤ m0 := hm0 ▸ le_trans hcL (le_max_right _ _)
  by_cases he : m0 % 2 = 0
  · have hb : (m0 % 2 == 0) = true := by simp [he]
    rw [if_pos hb]
    refine ⟨by omega, Nat.dvd_add hm0d (dvd_refl p), by omega, by omega, ?_⟩
    intro n hn hpn hLn hpp
    have h1 := hm0min n hpn hLn hpp
    have h2 : m0 ≠ n := by omega
    obtain ⟨a, rfl⟩ := hm0d; obtain ⟨b, rfl⟩ := hpn
    have : a < b := by
      by_contra hab; rw [not_lt] at hab
      have := Nat.mul_le_mul_left p hab; omega
    have := Nat.mul_le_mul_left p (show a + 1 ≤ b by omega); rw [Nat.mul_add, Nat.mul_one] at this; exact this
  · have hb : (m0 % 2 == 0) = false := by simp [he]
    rw [if_neg (by simp [hb])]
    exact ⟨by omega, hm0d, hm0L, hm0p, fun n _ h1 h2 h3 => hm0min n h1 h2 h3⟩

/-- **Soundness of the prime-multiple mask.** -/
theorem pmask_testBit {L W p : ℕ} (hL : L % 2 = 1) (hp : p % 2 = 1) (i : ℕ) :
    (pmask L W p).testBit i = decide (i < W ∧ p ∣ L + 2 * i ∧ p * p ≤ L + 2 * i) := by
  obtain ⟨hmo, hmd, hmL, hmp, hmin⟩ := fm_spec hL hp
  have hp0 : 0 < p := by omega
  rw [pmask_eq]
  generalize fm L p = m at hmo hmd hmL hmp hmin
  split_ifs with hz
  · rw [Nat.zero_testBit]; symm; rw [decide_eq_false_iff_not]
    rintro ⟨hi, hd, hpp⟩
    have := hmin _ (by omega) hd (by omega) hpp; omega
  · generalize hi0 : (m - L) / 2 = i0
    have hm : m = L + 2 * i0 := by omega
    have hi0W : i0 < W := by omega
    rw [Nat.testBit_shiftLeft, geom_eq_encF (by omega),
      encF_testBit hp0 _ _ (fun _ => Nat.one_lt_two_pow (by omega))]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
    have hcop : Nat.Coprime p 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 hp)
    constructor
    · rintro ⟨hge, hq, hr⟩
      obtain ⟨q, hq'⟩ : p ∣ i - i0 := Nat.dvd_of_mod_eq_zero hr
      have hiq : i = i0 + p * q := by omega
      have hqle : q ≤ (W - 1 - i0) / p := by
        have : (i - i0) / p = q := by rw [hq']; exact Nat.mul_div_cancel_left q hp0
        omega
      have hpq : p * q ≤ W - 1 - i0 := by
        have := Nat.div_mul_le_self (W - 1 - i0) p
        have := Nat.mul_le_mul_left p hqle; rw [mul_comm p ((W - 1 - i0) / p)] at this; omega
      refine ⟨by omega, ?_, by omega⟩
      rw [show L + 2 * i = m + p * (2 * q) by rw [hm, hiq]; ring]
      exact Nat.dvd_add hmd (Dvd.intro _ rfl)
    · rintro ⟨hiW, hd, hpp⟩
      have hle := hmin _ (by omega) hd (by omega) hpp
      have hge : i0 ≤ i := by omega
      have h2 : p ∣ (i - i0) * 2 := by
        have : (L + 2 * i) - m = (i - i0) * 2 := by omega
        rw [← this]; exact Nat.dvd_sub hd hmd
      have h3 : p ∣ i - i0 := hcop.dvd_of_dvd_mul_right h2
      refine ⟨hge, ?_, Nat.mod_eq_zero_of_dvd h3⟩
      have := Nat.div_le_div_right (c := p) (show i - i0 ≤ W - 1 - i0 by omega)
      omega

end ThetaSieve
-- ===== inlined from thetasieve/SieveSound =====

/-! Soundness of the segmented sieve `ThetaSieve.countSeg`: it counts the primes `L + 2 i`, `i < W`. -/

set_option autoImplicit false

namespace ThetaSieve

/-- Strictly increasing list check. -/
def sortedB : List ℕ → Bool
  | p :: q :: r => decide (p < q) && sortedB (q :: r)
  | _ => true

lemma sortedB_tail {p : ℕ} {ps : List ℕ} (h : sortedB (p :: ps) = true) : sortedB ps = true := by
  match ps, h with
  | [], _ => rfl
  | q :: r, h => simp only [sortedB, Bool.and_eq_true] at h; exact h.2

lemma sortedB_head : ∀ {p : ℕ} {ps : List ℕ}, sortedB (p :: ps) = true → ∀ q ∈ ps, p < q
  | _, [], _, q, hq => by simp at hq
  | p, r :: rs, h, q, hq => by
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1
    · exact lt_trans h.1 (sortedB_head h.2 q hq)

/-- Every entry is odd and at least `3`. -/
def oddB (ps : List ℕ) : Bool := ps.all (fun p => p % 2 == 1 && decide (3 ≤ p))

lemma oddB_mem {ps : List ℕ} (h : oddB ps = true) {p : ℕ} (hp : p ∈ ps) : p % 2 = 1 ∧ 3 ≤ p := by
  have := List.all_eq_true.1 h p hp
  simpa [Bool.and_eq_true] using this

/-- **Soundness of the composite mask** (any sorted list of odd numbers `≥ 3`). -/
theorem compMask_testBit {L W : ℕ} (hL : L % 2 = 1) (i : ℕ) : ∀ (ps : List ℕ), sortedB ps = true → oddB ps = true →
    (compMask L W ps).testBit i = decide (i < W ∧ ∃ p ∈ ps, p ∣ L + 2 * i ∧ p * p ≤ L + 2 * i)
  | [], _, _ => by simp [compMask]
  | p :: ps, hs, ho => by
    have hpo := oddB_mem ho List.mem_cons_self
    have ho' : oddB ps = true := by
      unfold oddB at ho ⊢; rw [List.all_cons, Bool.and_eq_true] at ho; exact ho.2
    unfold compMask
    split_ifs with hz
    · rw [Nat.zero_testBit]; symm; rw [decide_eq_false_iff_not]
      rintro ⟨hi, q, hq, _, hqq⟩
      have hpq : p ≤ q := by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact le_refl _
        · exact (sortedB_head hs q hq).le
      have := Nat.mul_le_mul hpq hpq; omega
    · rw [Nat.testBit_or, pmask_testBit hL hpo.1, compMask_testBit hL i ps (sortedB_tail hs) ho']
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, q, hq, h2, h3⟩)
        · exact ⟨h1, p, Or.inl rfl, h2, h3⟩
        · exact ⟨h1, q, Or.inr hq, h2, h3⟩
      · rintro ⟨h1, q, rfl | hq, h2, h3⟩
        · exact Or.inl ⟨h1, h2, h3⟩
        · exact Or.inr ⟨h1, q, hq, h2, h3⟩

lemma smallPrimes_sorted : sortedB smallPrimes = true := by decide +kernel
lemma smallPrimes_odd : oddB smallPrimes = true := by decide +kernel

/-- Survivor bits: `i < W` and no listed `p` with `p * p ≤ L + 2 i` divides `L + 2 i`. -/
theorem survivors_testBit {L W : ℕ} (hL : L % 2 = 1) (i : ℕ) :
    (survivors L W).testBit i =
      decide (i < W ∧ ¬ ∃ p ∈ smallPrimes, p ∣ L + 2 * i ∧ p * p ≤ L + 2 * i) := by
  unfold survivors
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, compMask_testBit hL i _ smallPrimes_sorted smallPrimes_odd]
  by_cases hi : i < W <;> by_cases hx : ∃ p ∈ smallPrimes, p ∣ L + 2 * i ∧ p * p ≤ L + 2 * i <;> simp [hi, hx]

lemma survivors_lt {L W : ℕ} (hL : L % 2 = 1) : survivors L W < 2 ^ W :=
  Nat.lt_pow_two_of_testBit _ (fun i hi => by rw [survivors_testBit hL]; simp; omega)

/-- Bitmap of a list of odd numbers: bit `(q - 3) / 2` for each `q`. -/
def bitmap : List ℕ → ℕ
  | [] => 0
  | q :: qs => (1 <<< ((q - 3) / 2)) ||| bitmap qs

lemma bitmap_mem : ∀ (qs : List ℕ), oddB qs = true → ∀ i, (bitmap qs).testBit i = true → 3 + 2 * i ∈ qs
  | [], _, i, h => by simp [bitmap] at h
  | q :: qs, ho, i, h => by
    have hq := oddB_mem ho List.mem_cons_self
    have ho' : oddB qs = true := by
      unfold oddB at ho ⊢; rw [List.all_cons, Bool.and_eq_true] at ho; exact ho.2
    rw [bitmap, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, Nat.testBit_one_eq_true_iff_self_eq_zero] at h
      have : i = (q - 3) / 2 := by simp at h; omega
      rw [List.mem_cons]; left; omega
    · exact List.mem_cons_of_mem _ (bitmap_mem qs ho' i h)

/-- Kernel certificate: the sieve of `[3, 60001)` coincides with the bitmap of `smallPrimes`. -/
lemma smallPrimes_bitmap : survivors 3 29999 = bitmap smallPrimes := by decide +kernel

/-- **Completeness of `smallPrimes`**: every prime `3 ≤ q < 60001` is listed. -/
theorem smallPrimes_complete {q : ℕ} (hq : q.Prime) (h3 : 3 ≤ q) (h6 : q < 60001) : q ∈ smallPrimes := by
  have hodd : q % 2 = 1 := by
    by_contra h
    have := hq.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)); omega
  have hq' : 3 + 2 * ((q - 3) / 2) = q := by omega
  have hi : (survivors 3 29999).testBit ((q - 3) / 2) = true := by
    rw [survivors_testBit (by norm_num), decide_eq_true_eq, hq']
    refine ⟨by omega, ?_⟩
    rintro ⟨p, hp, hd, hpp⟩
    have hp3 := (oddB_mem smallPrimes_odd hp).2
    rcases hq.eq_one_or_self_of_dvd p hd with h | h
    · omega
    · subst h; nlinarith
  rw [smallPrimes_bitmap] at hi
  have := bitmap_mem _ smallPrimes_odd _ hi
  rwa [hq'] at this

/-- **Survivor bits are exactly the primes.** -/
theorem survivors_prime {L W : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001) {i : ℕ}
    (hi : i < W) : (survivors L W).testBit i = true ↔ (L + 2 * i).Prime := by
  rw [survivors_testBit hL, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hno⟩
    by_contra hnp
    set n := L + 2 * i with hn
    have hn1 : n ≠ 1 := by omega
    have hq := Nat.minFac_prime hn1
    have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
    have hq2 : n.minFac ≠ 2 := by
      intro h2
      have := Nat.minFac_dvd n; rw [h2] at this; omega
    have hq3 : 3 ≤ n.minFac := by have := hq.two_le; omega
    have hq6 : n.minFac < 60001 := by
      by_contra h; rw [not_lt] at h
      have := Nat.mul_le_mul h h; rw [sq] at hsq; omega
    exact hno ⟨_, smallPrimes_complete hq hq3 hq6, Nat.minFac_dvd n, by rw [← sq]; exact hsq⟩
  · intro hp
    refine ⟨hi, ?_⟩
    rintro ⟨p, hmem, hd, hpp⟩
    have hp3 := (oddB_mem smallPrimes_odd hmem).2
    rcases hp.eq_one_or_self_of_dvd p hd with h | h
    · omega
    · rw [h] at hpp; nlinarith [hp.two_le]

/-- **Soundness of the segment count**: `countSeg L W` is the number of primes `L + 2 i` with `i < W`. -/
theorem countSeg_eq {L W : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001) :
    countSeg L W = ((Finset.range W).filter (fun i => (L + 2 * i).Prime)).card := by
  unfold countSeg
  rw [popcountW_eq (survivors_lt hL)]
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact survivors_prime hL h3 hB (Finset.mem_range.1 hi)

end ThetaSieve
-- ===== inlined from thetasieve/CertSound =====

/-! Soundness of the θ certificate checker. -/

set_option autoImplicit false

open Real Finset

namespace ThetaSieve

/-- `θ` at a natural number. -/
noncomputable def th (n : ℕ) : ℝ := Chebyshev.theta n

lemma th_succ (n : ℕ) : th (n + 1) = th n + if (n + 1).Prime then Real.log (n + 1) else 0 := by
  unfold th Chebyshev.theta
  rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  push_cast; rfl

/-- Weighted odd block. -/
noncomputable def oblock (a w : ℕ) : ℝ := ∑ i ∈ range w, if (a + 2 * i).Prime then Real.log (a + 2 * i : ℕ) else 0

lemma th_block {a : ℕ} (ha : 3 ≤ a) (hodd : a % 2 = 1) : ∀ w, th (a + 2 * w - 1) = th (a - 1) + oblock a w := by
  intro w
  induction w with
  | zero => simp [oblock]
  | succ w ih =>
    have e1 : a + 2 * (w + 1) - 1 = (a + 2 * w - 1 + 1) + 1 := by omega
    have e2 : a + 2 * w - 1 + 1 = a + 2 * w := by omega
    have hs : oblock a (w + 1) = oblock a w + (if (a + 2 * w).Prime then Real.log (a + 2 * w : ℕ) else 0) :=
      Finset.sum_range_succ _ _
    have hne : ¬ (a + 2 * w + 1).Prime := by
      intro hp
      have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)); omega
    rw [e1, th_succ, th_succ, ih, hs, e2, if_neg hne,
      show ((a + 2 * w - 1 : ℕ) : ℝ) + 1 = ((a + 2 * w : ℕ) : ℝ) by rw [← Nat.cast_add_one, e2]]
    ring

/-- Count of primes in an odd block. -/
def ocount (a w : ℕ) : ℕ := ((range w).filter (fun i => (a + 2 * i).Prime)).card

lemma oblock_bounds {a w : ℕ} (ha : 1 ≤ a) :
    (ocount a w : ℝ) * Real.log a ≤ oblock a w ∧ oblock a w ≤ (ocount a w : ℝ) * Real.log (a + 2 * w : ℕ) := by
  unfold oblock ocount
  rw [← Finset.sum_filter]
  have hc : ∀ i ∈ (range w).filter (fun i => (a + 2 * i).Prime),
      Real.log a ≤ Real.log (a + 2 * i : ℕ) ∧ Real.log (a + 2 * i : ℕ) ≤ Real.log (a + 2 * w : ℕ) := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    have h0 : (0 : ℝ) < a := by exact_mod_cast ha
    have hiw : (i : ℝ) ≤ w := by exact_mod_cast hi.1.le
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    constructor
    · exact Real.log_le_log h0 (by push_cast; linarith)
    · exact Real.log_le_log (by push_cast; positivity) (by push_cast; linarith)
  refine ⟨?_, ?_⟩
  · have := Finset.card_nsmul_le_sum _ _ _ (fun i hi => (hc i hi).1)
    simpa [nsmul_eq_mul] using this
  · have := Finset.sum_le_card_nsmul _ _ _ (fun i hi => (hc i hi).2)
    simpa [nsmul_eq_mul] using this

/-! Logarithm bounds. -/

lemma Q_pos : (0 : ℝ) < Q := by unfold Q; positivity

lemma LLo_le {n : ℕ} (hn : 1 ≤ n) : (LLo n : ℝ) ≤ Q * Real.log n := by
  have h := DusartCert.log_bounds Q n 1 (Nat.log2 n) (by
    simp only [DusartCert.redOK, Bool.and_eq_true, decide_eq_true_eq, one_mul]
    exact ⟨⟨Nat.log2_self_le (by omega), by have := @Nat.lt_log2_self n; rw [pow_succ] at this; omega⟩, one_pos⟩)
  simpa [LLo] using h.1

lemma le_LHi {n : ℕ} (hn : 1 ≤ n) : Q * Real.log n ≤ (LHi n : ℝ) := by
  have h := DusartCert.log_bounds Q n 1 (Nat.log2 n) (by
    simp only [DusartCert.redOK, Bool.and_eq_true, decide_eq_true_eq, one_mul]
    exact ⟨⟨Nat.log2_self_le (by omega), by have := @Nat.lt_log2_self n; rw [pow_succ] at this; omega⟩, one_pos⟩)
  simpa [LHi] using h.2

/-! Products of chunks. -/

lemma prodSmall_eq : ∀ (k L x : ℕ), prodSmall k L x = ∏ i ∈ range k, if x.testBit i then L + 2 * i else 1 := by
  intro k
  induction k with
  | zero => intro L x; rfl
  | succ k ih =>
    intro L x
    rw [prodSmall, ih, Finset.prod_range_succ']
    have h0 : (x % 2 = 1) = (x.testBit 0 = true) := by rw [Nat.testBit_zero]; simp
    rw [mul_comm]
    congr 1
    · apply Finset.prod_congr rfl; intro i _
      rw [Nat.testBit_div_two]; congr 1; ring
    · by_cases h : x % 2 = 1
      · have : x.testBit 0 = true := by rw [Nat.testBit_zero]; simp [h]
        simp [h, this]
      · have : x.testBit 0 = false := by rw [Nat.testBit_zero]; simp [h]
        simp [h, this]

/-! The allowance `h t = t / (5 log² t)` and the mesh cell. -/

/-- The allowance. -/
noncomputable def hh (t : ℝ) : ℝ := (1 / 5) * t / Real.log t ^ 2

lemma hh_mono {x y : ℝ} (hx0 : 0 < x) (hx : 2 ≤ Real.log x) (hxy : x ≤ y) : hh x ≤ hh y := by
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hLM : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  set L := Real.log x with hL
  set M := Real.log y with hM
  have hy : y = x * Real.exp (M - L) := by rw [Real.exp_sub, hM, hL, Real.exp_log hy0, Real.exp_log hx0]; field_simp
  have h1 : M ≤ L * (1 + (M - L) / 2) := by nlinarith
  have h2 : (1 + (M - L) / 2) ^ 2 ≤ Real.exp (M - L) := by
    have h3 := Real.add_one_le_exp ((M - L) / 2)
    calc (1 + (M - L) / 2) ^ 2 ≤ Real.exp ((M - L) / 2) ^ 2 := by
          apply pow_le_pow_left₀ (by linarith) (by linarith)
      _ = Real.exp (M - L) := by rw [sq, ← Real.exp_add]; ring_nf
  have hM2 : M ^ 2 ≤ L ^ 2 * Real.exp (M - L) := by
    calc M ^ 2 ≤ (L * (1 + (M - L) / 2)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      _ = L ^ 2 * (1 + (M - L) / 2) ^ 2 := by ring
      _ ≤ L ^ 2 * Real.exp (M - L) := mul_le_mul_of_nonneg_left h2 (by positivity)
  unfold hh
  rw [← hM, ← hL, div_le_div_iff₀ (by positivity) (by nlinarith), hy]
  have := mul_le_mul_of_nonneg_left hM2 hx0.le
  calc 1 / 5 * x * M ^ 2 = 1 / 5 * (x * M ^ 2) := by ring
    _ ≤ 1 / 5 * (x * (L ^ 2 * Real.exp (M - L))) := by gcongr
    _ = 1 / 5 * (x * Real.exp (M - L)) * L ^ 2 := by ring

lemma hh_sub {x y : ℝ} (hx0 : 0 < x) (hx : 2 ≤ Real.log x) (hxy : x ≤ y) : hh y - hh x ≤ y - x := by
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hLM : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hL2 : 0 < Real.log x ^ 2 := by positivity
  have hyle : hh y ≤ (1 / 5) * y / Real.log x ^ 2 := by
    unfold hh
    apply div_le_div_of_nonneg_left (by positivity) hL2 (pow_le_pow_left₀ (by linarith) hLM 2)
  have : (1 / 5) * y / Real.log x ^ 2 - hh x = (y - x) / (5 * Real.log x ^ 2) := by unfold hh; field_simp
  have h20 : 1 ≤ 5 * Real.log x ^ 2 := by nlinarith
  have hyx : 0 ≤ y - x := by linarith
  have : (y - x) / (5 * Real.log x ^ 2) ≤ y - x := div_le_self hyx h20
  linarith

lemma two_le_log {x : ℝ} (hx : 8 ≤ x) : 2 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]; nlinarith [Real.exp_pos 1]

/-- The bound on `[a, b)`. -/
def Good (a b : ℕ) : Prop :=
  ∀ t : ℝ, (a : ℝ) ≤ t → t < b → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2

/-- **Mesh cell.** -/
lemma cell {a b : ℕ} (ha : 8 ≤ a) (hlow : (b : ℝ) - hh b ≤ th a) (hup : th (b - 1) ≤ (a : ℝ) + hh a) :
    Good a b := by
  intro t hat htb
  have ha8 : (8 : ℝ) ≤ a := by exact_mod_cast ha
  have ht0 : 0 < t := by linarith
  have hfl1 : a ≤ ⌊t⌋₊ := Nat.le_floor hat
  have hfl2 : ⌊t⌋₊ ≤ b - 1 := by
    have := Nat.floor_lt (ht0.le) |>.2 htb; omega
  have hθ : Chebyshev.theta t = th ⌊t⌋₊ := Chebyshev.theta_eq_theta_coe_floor t
  have hm1 : th a ≤ th ⌊t⌋₊ := Chebyshev.theta_mono (by exact_mod_cast hfl1)
  have hm2 : th ⌊t⌋₊ ≤ th (b - 1) := Chebyshev.theta_mono (by exact_mod_cast hfl2)
  have hla := two_le_log ha8
  have hlt := two_le_log (le_trans ha8 hat)
  have s1 := hh_sub ht0 hlt htb.le
  have s2 := hh_mono (by linarith) hla hat
  show |Chebyshev.theta t - t| ≤ hh t
  rw [abs_le, hθ]
  constructor <;> linarith

/-- `lowOK` read over the reals. -/
lemma low_real {lo b H : ℕ} (h : lowOK lo b H = true) (hb : 2 ≤ b) (hH : (Q : ℝ) * Real.log b ≤ H) :
    (b : ℝ) - hh b ≤ lo / Q := by
  unfold lowOK at h
  have h' : ((Q * b * (5 * H ^ 2) : ℕ) : ℝ) ≤ ((lo * (5 * H ^ 2) + Q ^ 3 * b : ℕ) : ℝ) := by
    exact_mod_cast (of_decide_eq_true h)
  push_cast at h'
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hL : 0 < Real.log b := Real.log_pos (by linarith)
  have hQ := Q_pos
  have hH0 : 0 < (H : ℝ) := lt_of_lt_of_le (by positivity) hH
  have hLH : Real.log b ≤ H / Q := by rw [le_div_iff₀ hQ]; linarith
  have hhb : (b : ℝ) * Q ^ 2 / (5 * H ^ 2) ≤ hh b := by
    unfold hh
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : Real.log b ^ 2 * Q ^ 2 ≤ (H : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ hL.le hLH 2
      rw [div_pow, le_div_iff₀ (by positivity)] at this; linarith
    nlinarith [this, (by positivity : (0 : ℝ) ≤ b)]
  have key : (b : ℝ) - b * Q ^ 2 / (5 * H ^ 2) ≤ lo / Q := by
    rw [sub_le_iff_le_add, div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `upOK` read over the reals. -/
lemma up_real {hi a H : ℕ} (h : upOK hi a H = true) (ha : 2 ≤ a) (hH : (Q : ℝ) * Real.log a ≤ H) :
    (hi : ℝ) / Q ≤ a + hh a := by
  unfold upOK at h
  have h' : ((hi * (5 * H ^ 2) : ℕ) : ℝ) ≤ ((Q * a * (5 * H ^ 2) + Q ^ 3 * a : ℕ) : ℝ) := by
    exact_mod_cast (of_decide_eq_true h)
  push_cast at h'
  have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hL : 0 < Real.log a := Real.log_pos (by linarith)
  have hQ := Q_pos
  have hH0 : 0 < (H : ℝ) := lt_of_lt_of_le (by positivity) hH
  have hLH : Real.log a ≤ H / Q := by rw [le_div_iff₀ hQ]; linarith
  have hha : (a : ℝ) * Q ^ 2 / (5 * H ^ 2) ≤ hh a := by
    unfold hh
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : Real.log a ^ 2 * Q ^ 2 ≤ (H : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ hL.le hLH 2
      rw [div_pow, le_div_iff₀ (by positivity)] at this; linarith
    nlinarith [this, (by positivity : (0 : ℝ) ≤ a)]
  have key : (hi : ℝ) / Q ≤ a + a * Q ^ 2 / (5 * H ^ 2) := by
    rw [div_le_iff₀ hQ]
    have e : ((a : ℝ) + a * Q ^ 2 / (5 * H ^ 2)) * Q = (Q * a * (5 * H ^ 2) + Q ^ 3 * a) / (5 * H ^ 2) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  linarith

/-! Windows and segments. -/

/-- Fixed-point bounds for `θ(a-1)`. -/
def Inv (lo hi a : ℕ) : Prop := (lo : ℝ) ≤ Q * th (a - 1) ∧ Q * th (a - 1) ≤ hi

lemma Good_trans {a b c : ℕ} (h1 : Good a b) (h2 : Good b c) : Good a c := by
  intro t hat htc
  rcases lt_or_ge t b with h | h
  · exact h1 t hat h
  · exact h2 t h htc

lemma Good_refl (a : ℕ) : Good a a := fun t h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

lemma window_count {L W off w : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001)
    (hw : off + w ≤ W) : popcountW w ((survivors L W >>> off) % 2 ^ w) = ocount (L + 2 * off) w := by
  rw [popcountW_eq (Nat.mod_lt _ (Nat.two_pow_pos w))]
  unfold ocount
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [hi, decide_true, Bool.true_and]
  rw [survivors_prime hL h3 hB (by omega : off + i < W), show L + 2 * (off + i) = L + 2 * off + 2 * i by ring]

lemma window_first {L W off : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001)
    (hw : off < W) : (survivors L W >>> off) % 2 = 1 ↔ (L + 2 * off).Prime := by
  rw [← survivors_prime hL h3 hB hw]
  have h := Nat.testBit_shiftRight (i := off) (j := 0) (survivors L W)
  rw [Nat.testBit_zero, Nat.add_zero] at h
  rw [← h, decide_eq_true_iff]

lemma th_at {a : ℕ} (ha : 1 ≤ a) : th a = th (a - 1) + if a.Prime then Real.log a else 0 := by
  have := th_succ (a - 1)
  rw [Nat.sub_add_cancel ha] at this
  rw [this]; push_cast [Nat.cast_sub ha]; simp

theorem runWin_sound {L W : ℕ} (hL : L % 2 = 1) (h8 : 8 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001) :
    ∀ (ws : List ℕ) (lo hi off lo' hi' : ℕ), off + ws.sum ≤ W →
      runWin lo hi (L + 2 * off) (survivors L W >>> off) ws = some (lo', hi') → Inv lo hi (L + 2 * off) →
      Inv lo' hi' (L + 2 * (off + ws.sum)) ∧ Good (L + 2 * off) (L + 2 * (off + ws.sum)) := by
  intro ws
  induction ws with
  | nil =>
    intro lo hi off lo' hi' _ h hI
    simp only [runWin, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.sum_nil, Nat.add_zero]; exact ⟨hI, Good_refl _⟩
  | cons w ws ih =>
    intro lo hi off lo' hi' hsum h hI
    rw [List.sum_cons] at hsum ⊢
    rw [runWin] at h
    generalize hlo1 : (if (survivors L W >>> off) % 2 = 1 then lo + LLo (L + 2 * off) else lo) = lo1 at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hw0, hlow⟩, hup⟩ := hc
    set a := L + 2 * off with ha_def
    set b := a + 2 * w with hb_def
    have hodd : a % 2 = 1 := by omega
    have ha8 : 8 ≤ a := by omega
    have hcnt := window_count hL (by omega) hB (show off + w ≤ W by omega)
    rw [← ha_def] at hcnt
    rw [hcnt] at h hup
    have hblk := th_block (a := a) (by omega) hodd w
    have hbd := oblock_bounds (a := a) (w := w) (by omega)
    have hLa := LLo_le (n := a) (by omega)
    have hHb := le_LHi (n := b) (by omega)
    have hHa := le_LHi (n := a) (by omega)
    have hQ := Q_pos
    have hc0 : (0 : ℝ) ≤ ocount a w := Nat.cast_nonneg _
    -- the new invariant at b
    have hInvb : Inv (lo + ocount a w * LLo a) (hi + ocount a w * LHi b) b := by
      unfold Inv at hI ⊢
      rw [show b - 1 = a + 2 * w - 1 by omega, hblk]
      push_cast
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hLa hc0]
      · have : (ocount a w : ℝ) * (Q * Real.log b) ≤ ocount a w * LHi b := mul_le_mul_of_nonneg_left hHb hc0
        have hb' : ((a + 2 * w : ℕ) : ℝ) = b := by rw [hb_def]
        rw [hb'] at hbd
        nlinarith
    -- the cell
    have hgood : Good a b := by
      apply cell ha8
      · have hl := low_real hlow (by omega) hHb
        have hfirst := window_first hL (by omega) hB (show off < W by omega)
        rw [← ha_def] at hfirst
        rw [th_at (by omega)]
        unfold Inv at hI
        have hth : th (a - 1) ≥ (lo : ℝ) / Q := by rw [ge_iff_le, div_le_iff₀ hQ]; linarith [hI.1]
        by_cases hx : (survivors L W >>> off) % 2 = 1
        · rw [if_pos hx] at hlo1
          subst hlo1
          have hp := hfirst.1 hx
          rw [if_pos hp]; push_cast at hl
          have : ((lo : ℝ) + LLo a) / Q ≤ th (a - 1) + Real.log a := by
            rw [div_le_iff₀ hQ]; nlinarith [hI.1]
          linarith
        · by_cases hp : a.Prime
          · exact absurd (hfirst.2 hp) hx
          · rw [if_neg hx] at hlo1
            subst hlo1
            rw [if_neg hp]; linarith
      · have hu := up_real hup (by omega) hHa
        have := hInvb.2
        rw [div_le_iff₀ hQ] at hu
        push_cast at hu this
        have : Q * th (b - 1) ≤ Q * ((a : ℝ) + hh a) := by linarith
        exact le_of_mul_le_mul_left this hQ
    -- recurse
    have hrec := ih (lo + ocount a w * LLo a) (hi + ocount a w * LHi b) (off + w) lo' hi' (by omega)
      (by rw [show L + 2 * (off + w) = b by omega, Nat.shiftRight_add]; exact h)
      (by rw [show L + 2 * (off + w) = b by omega]; exact hInvb)
    rw [show off + w + ws.sum = off + (w + ws.sum) by ring, show L + 2 * (off + w) = b by omega] at hrec
    exact ⟨hrec.1, Good_trans hgood hrec.2⟩

/-! Base chunks. -/

lemma chunk_prod {L W off w : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001)
    (hw : off + w ≤ W) : prodSmall w (L + 2 * off) ((survivors L W >>> off) % 2 ^ w) =
      ∏ i ∈ range w, if (L + 2 * off + 2 * i).Prime then L + 2 * off + 2 * i else 1 := by
  rw [prodSmall_eq]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [hi, decide_true, Bool.true_and]
  have := survivors_prime hL h3 hB (show off + i < W by omega)
  rw [show L + 2 * (off + i) = L + 2 * off + 2 * i by ring] at this
  by_cases hp : (L + 2 * off + 2 * i).Prime
  · rw [if_pos (this.2 hp), if_pos hp]
  · have : ¬ (survivors L W).testBit (off + i) = true := fun h => hp (this.1 h)
    rw [if_neg this, if_neg hp]

lemma log_chunk (a w : ℕ) (ha : 1 ≤ a) :
    Real.log ((∏ i ∈ range w, if (a + 2 * i).Prime then a + 2 * i else 1 : ℕ) : ℝ) = oblock a w := by
  rw [Nat.cast_prod, Real.log_prod]
  · unfold oblock
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  · intro i _
    exact Nat.cast_ne_zero.2 (by split_ifs <;> omega)

theorem accSeg_sound {L W : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001) :
    ∀ (n lo hi off rem lo' hi' : ℕ), off + rem = W → rem ≤ 64 * n →
      accSeg lo hi (L + 2 * off) (survivors L W >>> off) rem n = (lo', hi') → Inv lo hi (L + 2 * off) →
      Inv lo' hi' (L + 2 * W) := by
  intro n
  induction n with
  | zero =>
    intro lo hi off rem lo' hi' hsum hrem h hI
    simp only [accSeg, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [show W = off by omega]; exact hI
  | succ n ih =>
    intro lo hi off rem lo' hi' hsum hrem h hI
    rw [accSeg] at h
    split_ifs at h with h0
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [show W = off by omega]; exact hI
    · dsimp only at h
      set w := min 64 rem with hw
      set a := L + 2 * off with ha_def
      have hw1 : off + w ≤ W := by omega
      rw [chunk_prod hL h3 hB hw1] at h
      have hP := log_chunk a w (by omega)
      have hPpos : 1 ≤ (∏ i ∈ range w, if (a + 2 * i).Prime then a + 2 * i else 1) := by
        apply Finset.one_le_prod'' ; intro i; split_ifs <;> omega
      have hlo := LLo_le hPpos
      have hhi := le_LHi hPpos
      rw [hP] at hlo hhi
      have hblk := th_block (a := a) (by omega) (by omega) w
      have hInv : Inv (lo + LLo (∏ i ∈ range w, if (a + 2 * i).Prime then a + 2 * i else 1))
          (hi + LHi (∏ i ∈ range w, if (a + 2 * i).Prime then a + 2 * i else 1)) (L + 2 * (off + w)) := by
        unfold Inv at hI ⊢
        rw [show L + 2 * (off + w) - 1 = a + 2 * w - 1 by omega, hblk]
        push_cast
        constructor <;> nlinarith [hI.1, hI.2]
      exact ih _ _ (off + w) (rem - w) lo' hi' (by omega) (by omega)
        (by rw [show L + 2 * (off + w) = a + 2 * w by omega, Nat.shiftRight_add]; exact h) hInv

/-! Records and chains. -/

theorem seg_sound (s : Seg) (h : s.ok = true) (hI : Inv s.lo s.hi s.L) :
    Inv s.lo' s.hi' (s.L + 2 * s.W) ∧ Good s.L (s.L + 2 * s.W) := by
  unfold Seg.ok runSeg at h
  split_ifs at h with hr
  · simp only [segRange, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
    obtain ⟨⟨⟨hL, h8⟩, hB⟩, hsum⟩ := hr
    have h' : runWin s.lo s.hi s.L (survivors s.L s.W) s.ws = some (s.lo', s.hi') := by simpa using h
    have := runWin_sound hL h8 hB s.ws s.lo s.hi 0 s.lo' s.hi' (by omega) (by simpa using h') (by simpa using hI)
    simpa [hsum] using this
  · simp at h

theorem bseg_sound (s : Seg) (h : s.bok = true) (hI : Inv s.lo s.hi s.L) : Inv s.lo' s.hi' (s.L + 2 * s.W) := by
  unfold Seg.bok baseSeg at h
  split_ifs at h with hr
  · simp only [segRange, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
    obtain ⟨⟨hL, h3⟩, hB⟩ := hr
    have h' : accSeg s.lo s.hi s.L (survivors s.L s.W) s.W (s.W / 64 + 1) = (s.lo', s.hi') := by simpa using h
    exact accSeg_sound hL h3 hB (s.W / 64 + 1) s.lo s.hi 0 s.W s.lo' s.hi' (by omega) (by omega)
      (by simpa using h') (by simpa using hI)
  · simp at h

/-- Last record of a chain. -/
def chainEnd : Seg → List Seg → Seg
  | s, [] => s
  | _, t :: r => chainEnd t r

theorem chain_sound : ∀ (l : List Seg) (s : Seg), chainOK (s :: l) = true → (∀ x ∈ s :: l, x.ok = true) →
    Inv s.lo s.hi s.L →
    Good s.L ((chainEnd s l).L + 2 * (chainEnd s l).W) ∧
      Inv (chainEnd s l).lo' (chainEnd s l).hi' ((chainEnd s l).L + 2 * (chainEnd s l).W) := by
  intro l
  induction l with
  | nil =>
    intro s _ hok hI
    have := seg_sound s (hok s List.mem_cons_self) hI
    exact ⟨this.2, this.1⟩
  | cons t r ih =>
    intro s hc hok hI
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, hc⟩ := hc
    have hs := seg_sound s (hok s List.mem_cons_self) hI
    have hIt : Inv t.lo t.hi t.L := by rw [← h1, ← h2, ← h3]; exact hs.1
    have := ih t hc (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hIt
    rw [← h1] at this
    exact ⟨Good_trans hs.2 this.1, this.2⟩

theorem bchain_sound : ∀ (l : List Seg) (s : Seg), chainOK (s :: l) = true → (∀ x ∈ s :: l, x.bok = true) →
    Inv s.lo s.hi s.L →
    Inv (chainEnd s l).lo' (chainEnd s l).hi' ((chainEnd s l).L + 2 * (chainEnd s l).W) := by
  intro l
  induction l with
  | nil => intro s _ hok hI; exact bseg_sound s (hok s List.mem_cons_self) hI
  | cons t r ih =>
    intro s hc hok hI
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, hc⟩ := hc
    have hs := bseg_sound s (hok s List.mem_cons_self) hI
    have hIt : Inv t.lo t.hi t.L := by rw [← h1, ← h2, ← h3]; exact hs
    exact ih t hc (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hIt

lemma Inv_three : Inv (LLo 2) (LHi 2) 3 := by
  have h2 : th 2 = Real.log 2 := by
    have e1 := th_succ 1
    have e0 := th_succ 0
    have hz : th 0 = 0 := by unfold th; simp
    rw [e0, hz] at e1
    rw [show (2 : ℕ) = 1 + 1 from rfl, e1]
    norm_num
  unfold Inv
  rw [show 3 - 1 = 2 from rfl, h2]
  exact ⟨by simpa using LLo_le (n := 2) (by norm_num), by simpa using le_LHi (n := 2) (by norm_num)⟩

/-- **Assembly**: base chain from `3`, mesh chain from `3594641`, linked, reaching past `3584912847`. -/
theorem theta_finite_of (b0 : Seg) (Br : List Seg) (m0 : Seg) (Mr : List Seg)
    (hbc : chainOK (b0 :: Br) = true) (hbok : ∀ x ∈ b0 :: Br, x.bok = true)
    (hb0 : b0.lo = LLo 2 ∧ b0.hi = LHi 2 ∧ b0.L = 3)
    (hlink : (chainEnd b0 Br).lo' = m0.lo ∧ (chainEnd b0 Br).hi' = m0.hi ∧
      (chainEnd b0 Br).L + 2 * (chainEnd b0 Br).W = m0.L)
    (hm0 : m0.L = 3594641) (hmc : chainOK (m0 :: Mr) = true) (hmok : ∀ x ∈ m0 :: Mr, x.ok = true)
    (hend : 3584912847 < (chainEnd m0 Mr).L + 2 * (chainEnd m0 Mr).W) :
    ∀ t : ℝ, 3594641 ≤ t → t ≤ 3584912847 → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2 := by
  have hI0 : Inv b0.lo b0.hi b0.L := by rw [hb0.1, hb0.2.1, hb0.2.2]; exact Inv_three
  have hIb := bchain_sound Br b0 hbc hbok hI0
  rw [hlink.1, hlink.2.1, hlink.2.2] at hIb
  have hG := (chain_sound Mr m0 hmc hmok hIb).1
  intro t h1 h2
  apply hG t (by rw [hm0]; exact_mod_cast h1)
  have : (3584912847 : ℝ) < ((chainEnd m0 Mr).L + 2 * (chainEnd m0 Mr).W : ℕ) := by exact_mod_cast hend
  linarith

end ThetaSieve
-- ===== inlined from PrimSound =====

/-! Soundness of a certificate for `primorial n * 25 ^ n < 68 ^ n` on a range of `n`.

A base chain of θ records (`Seg.bok`, the kernel-checked sieve and fixed-point logs of `ThetaSieve`) carries
`Inv lo hi a : lo ≤ Q θ(a-1) ≤ hi` from `a = 3` upward. On a segment `[L, L + 2W)` every `n` with `L - 1 ≤ n`
has `θ n ≤ θ(L + 2W - 1) ≤ hi' / Q`; if moreover `hi' < (L - 1) c` with `c ≤ Q log(68/25)`, then
`θ n < n log(68/25)`, i.e. `primorial n * 25 ^ n < 68 ^ n` (`Chebyshev.theta_eq_log_primorial`). -/

set_option autoImplicit false

open Real

namespace ThetaSieve

/-- The per-segment check: the θ upper bound at the segment end is below `(L - 1) c`. -/
def primOK (c : Nat) (s : Seg) : Bool := s.hi' < (s.L - 1) * c

/-- One segment: every `n` in `[L - 1, L + 2W - 1]` satisfies `Q θ n < n c`. -/
lemma prim_seg (c : Nat) (s : Seg) (hb : s.bok = true) (hI : Inv s.lo s.hi s.L) (hp : primOK c s = true)
    (n : ℕ) (hlo : s.L - 1 ≤ n) (hhi : n + 1 ≤ s.L + 2 * s.W) :
    (Q : ℝ) * th n < n * c := by
  have hE := (bseg_sound s hb hI).2
  have hmono : th n ≤ th (s.L + 2 * s.W - 1) := by
    unfold th; exact Chebyshev.theta_mono (by exact_mod_cast (by omega : n ≤ s.L + 2 * s.W - 1))
  have hp' : (s.hi' : ℝ) < ((s.L - 1 : ℕ) : ℝ) * c := by
    unfold primOK at hp; exact_mod_cast (by simpa using hp)
  have hQ : (0 : ℝ) ≤ Q := le_of_lt Q_pos
  have hc : (0 : ℝ) ≤ c := by positivity
  have hL : ((s.L - 1 : ℕ) : ℝ) * c ≤ (n : ℝ) * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hlo) hc
  calc (Q : ℝ) * th n ≤ Q * th (s.L + 2 * s.W - 1) := mul_le_mul_of_nonneg_left hmono hQ
    _ ≤ s.hi' := hE
    _ < ((s.L - 1 : ℕ) : ℝ) * c := hp'
    _ ≤ n * c := hL

/-- The chain: from `Inv` at the first record, every `n` past `A` and inside the chain's span satisfies
`Q θ n < n c`, provided every segment that reaches past `A + 1` passes `primOK`. -/
theorem prim_chain (c A : Nat) : ∀ (l : List Seg) (s : Seg), chainOK (s :: l) = true → (∀ x ∈ s :: l, x.bok = true) →
    (∀ x ∈ s :: l, A + 1 < x.L + 2 * x.W → primOK c x = true) → Inv s.lo s.hi s.L →
    ∀ n : ℕ, A < n → s.L - 1 ≤ n → n + 1 ≤ (chainEnd s l).L + 2 * (chainEnd s l).W → (Q : ℝ) * th n < n * c := by
  intro l
  induction l with
  | nil =>
    intro s _ hok hp hI n hA hlo hhi
    exact prim_seg c s (hok s List.mem_cons_self) hI (hp s List.mem_cons_self (by simp [chainEnd] at hhi; omega)) n hlo
      (by simpa [chainEnd] using hhi)
  | cons t r ih =>
    intro s hc hok hp hI n hA hlo hhi
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, hc⟩ := hc
    by_cases hin : n + 1 ≤ s.L + 2 * s.W
    · exact prim_seg c s (hok s List.mem_cons_self) hI (hp s List.mem_cons_self (by omega)) n hlo hin
    · have hs := bseg_sound s (hok s List.mem_cons_self) hI
      have hIt : Inv t.lo t.hi t.L := by rw [← h1, ← h2, ← h3]; exact hs
      exact ih t hc (fun x hx => hok x (List.mem_cons_of_mem _ hx)) (fun x hx => hp x (List.mem_cons_of_mem _ hx)) hIt n hA
        (by omega) (by simpa [chainEnd] using hhi)

/-- The constant: `LLo 68 - LHi 25 ≤ Q log(68/25)` (given `LHi 25 ≤ LLo 68`, which the kernel decides). -/
lemma c_le (h : LHi 25 ≤ LLo 68) : ((LLo 68 - LHi 25 : ℕ) : ℝ) ≤ Q * Real.log (68 / 25) := by
  have h68 := LLo_le (n := 68) (by norm_num)
  have h25 := le_LHi (n := 25) (by norm_num)
  rw [Nat.cast_sub h, Real.log_div (by norm_num) (by norm_num), mul_sub]
  push_cast at h68 h25 ⊢
  linarith

/-- From the θ bound to the primorial statement. -/
lemma primorial_of_theta (n : ℕ) (hn : 0 < n) (h : th n < n * Real.log (68 / 25)) : primorial n * 25 ^ n < 68 ^ n := by
  have hth : th n = Real.log (primorial n) := by
    unfold th; rw [Chebyshev.theta_eq_log_primorial]; simp
  rw [hth] at h
  have hP : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have key : Real.log ((primorial n : ℝ) * 25 ^ n) < Real.log ((68 : ℝ) ^ n) := by
    rw [Real.log_mul hP.ne' (by positivity), Real.log_pow, Real.log_pow,
      Real.log_div (by norm_num) (by norm_num)] at *
    nlinarith
  have := (Real.log_lt_log_iff (by positivity) (by positivity)).1 key
  exact_mod_cast this

/-- Everything together: a checked chain from `3` that reaches past `B`, with `primOK` on every segment past `A + 1`,
proves the statement on `(A, B]`. -/
theorem primorial_range_of (A B : Nat) (s : Seg) (l : List Seg)
    (hs : s.lo = LLo 2 ∧ s.hi = LHi 2 ∧ s.L = 3)
    (hc : chainOK (s :: l) = true) (hok : ∀ x ∈ s :: l, x.bok = true)
    (hp : ∀ x ∈ s :: l, A + 1 < x.L + 2 * x.W → primOK (LLo 68 - LHi 25) x = true)
    (hend : B + 1 ≤ (chainEnd s l).L + 2 * (chainEnd s l).W) (hcd : LHi 25 ≤ LLo 68) (hA : 2 ≤ A) :
    ∀ n : ℕ, A < n → n ≤ B → primorial n * 25 ^ n < 68 ^ n := by
  intro n hn hnB
  have hI : Inv s.lo s.hi s.L := by rw [hs.1, hs.2.1, hs.2.2]; exact Inv_three
  have hQ := prim_chain (LLo 68 - LHi 25) A l s hc hok hp hI n hn (by rw [hs.2.2]; omega) (by omega)
  have hcq := c_le hcd
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h2 : (Q : ℝ) * th n < Q * (n * Real.log (68 / 25)) := by
    calc (Q : ℝ) * th n < n * ((LLo 68 - LHi 25 : ℕ) : ℝ) := hQ
      _ ≤ n * (Q * Real.log (68 / 25)) := mul_le_mul_of_nonneg_left hcq hn0
      _ = Q * (n * Real.log (68 / 25)) := by ring
  exact primorial_of_theta n (by omega) (lt_of_mul_lt_mul_left h2 (le_of_lt Q_pos))

end ThetaSieve

namespace ThetaSieve
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def PAll : List Seg := PrimData0.segs ++ PrimData1.segs ++ PrimData2.segs ++ PrimData3.segs ++ PrimData4.segs ++ PrimData5.segs ++ PrimData6.segs ++ PrimData7.segs ++ PrimData8.segs ++ PrimData9.segs ++ PrimData10.segs ++ PrimData11.segs ++ PrimData12.segs ++ PrimData13.segs ++ PrimData14.segs ++ PrimData15.segs ++ PrimData16.segs ++ PrimData17.segs ++ PrimData18.segs ++ PrimData19.segs ++ PrimData20.segs ++ PrimData21.segs ++ PrimData22.segs ++ PrimData23.segs ++ PrimData24.segs ++ PrimData25.segs ++ PrimData26.segs ++ PrimData27.segs ++ PrimData28.segs ++ PrimData29.segs ++ PrimData30.segs ++ PrimData31.segs ++ PrimData32.segs ++ PrimData33.segs ++ PrimData34.segs ++ PrimData35.segs ++ PrimData36.segs ++ PrimData37.segs ++ PrimData38.segs ++ PrimData39.segs ++ PrimData40.segs ++ PrimData41.segs ++ PrimData42.segs ++ PrimData43.segs ++ PrimData44.segs ++ PrimData45.segs ++ PrimData46.segs ++ PrimData47.segs ++ PrimData48.segs ++ PrimData49.segs ++ PrimData50.segs ++ PrimData51.segs ++ PrimData52.segs ++ PrimData53.segs ++ PrimData54.segs ++ PrimData55.segs ++ PrimData56.segs ++ PrimData57.segs ++ PrimData58.segs ++ PrimData59.segs ++ PrimData60.segs ++ PrimData61.segs ++ PrimData62.segs ++ PrimData63.segs ++ PrimData64.segs ++ PrimData65.segs ++ PrimData66.segs ++ PrimData67.segs ++ PrimData68.segs ++ PrimData69.segs ++ PrimData70.segs ++ PrimData71.segs ++ PrimData72.segs ++ PrimData73.segs ++ PrimData74.segs

theorem PAll_bok : ∀ x ∈ PAll, x.bok = true := by
  unfold PAll
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨(PrimorialCert.block_0).1, (PrimorialCert.block_1).1⟩, (PrimorialCert.block_2).1⟩, (PrimorialCert.block_3).1⟩, (PrimorialCert.block_4).1⟩, (PrimorialCert.block_5).1⟩, (PrimorialCert.block_6).1⟩, (PrimorialCert.block_7).1⟩, (PrimorialCert.block_8).1⟩, (PrimorialCert.block_9).1⟩, (PrimorialCert.block_10).1⟩, (PrimorialCert.block_11).1⟩, (PrimorialCert.block_12).1⟩, (PrimorialCert.block_13).1⟩, (PrimorialCert.block_14).1⟩, (PrimorialCert.block_15).1⟩, (PrimorialCert.block_16).1⟩, (PrimorialCert.block_17).1⟩, (PrimorialCert.block_18).1⟩, (PrimorialCert.block_19).1⟩, (PrimorialCert.block_20).1⟩, (PrimorialCert.block_21).1⟩, (PrimorialCert.block_22).1⟩, (PrimorialCert.block_23).1⟩, (PrimorialCert.block_24).1⟩, (PrimorialCert.block_25).1⟩, (PrimorialCert.block_26).1⟩, (PrimorialCert.block_27).1⟩, (PrimorialCert.block_28).1⟩, (PrimorialCert.block_29).1⟩, (PrimorialCert.block_30).1⟩, (PrimorialCert.block_31).1⟩, (PrimorialCert.block_32).1⟩, (PrimorialCert.block_33).1⟩, (PrimorialCert.block_34).1⟩, (PrimorialCert.block_35).1⟩, (PrimorialCert.block_36).1⟩, (PrimorialCert.block_37).1⟩, (PrimorialCert.block_38).1⟩, (PrimorialCert.block_39).1⟩, (PrimorialCert.block_40).1⟩, (PrimorialCert.block_41).1⟩, (PrimorialCert.block_42).1⟩, (PrimorialCert.block_43).1⟩, (PrimorialCert.block_44).1⟩, (PrimorialCert.block_45).1⟩, (PrimorialCert.block_46).1⟩, (PrimorialCert.block_47).1⟩, (PrimorialCert.block_48).1⟩, (PrimorialCert.block_49).1⟩, (PrimorialCert.block_50).1⟩, (PrimorialCert.block_51).1⟩, (PrimorialCert.block_52).1⟩, (PrimorialCert.block_53).1⟩, (PrimorialCert.block_54).1⟩, (PrimorialCert.block_55).1⟩, (PrimorialCert.block_56).1⟩, (PrimorialCert.block_57).1⟩, (PrimorialCert.block_58).1⟩, (PrimorialCert.block_59).1⟩, (PrimorialCert.block_60).1⟩, (PrimorialCert.block_61).1⟩, (PrimorialCert.block_62).1⟩, (PrimorialCert.block_63).1⟩, (PrimorialCert.block_64).1⟩, (PrimorialCert.block_65).1⟩, (PrimorialCert.block_66).1⟩, (PrimorialCert.block_67).1⟩, (PrimorialCert.block_68).1⟩, (PrimorialCert.block_69).1⟩, (PrimorialCert.block_70).1⟩, (PrimorialCert.block_71).1⟩, (PrimorialCert.block_72).1⟩, (PrimorialCert.block_73).1⟩, (PrimorialCert.block_74).1⟩

theorem PAll_head : PAll = PrimData0.s0 :: PAll.tail := rfl
theorem PAll_s0 : PrimData0.s0.lo = LLo 2 ∧ PrimData0.s0.hi = LHi 2 ∧ PrimData0.s0.L = 3 := by decide +kernel
theorem PAll_chain : chainOK PAll = true := by decide +kernel
theorem cval : LLo 68 - LHi 25 = 18458400208034708012 := by decide +kernel
theorem cpos : LHi 25 ≤ LLo 68 := by decide +kernel
theorem PAll_prim : ∀ x ∈ PAll, 16000001 < x.L + 2 * x.W → primOK (LLo 68 - LHi 25) x = true := by
  rw [cval]; decide +kernel
theorem PAll_end : 24000000 + 1 ≤ (chainEnd PrimData0.s0 PAll.tail).L + 2 * (chainEnd PrimData0.s0 PAll.tail).W := by decide +kernel

end ThetaSieve

open ThetaSieve in
theorem solution (n : ℕ) (hn : 20000000 < n) (hn' : n ≤ 24000000) : primorial n * 25 ^ n < 68 ^ n := by
  have hok : ∀ x ∈ PrimData0.s0 :: PAll.tail, x.bok = true := by rw [← PAll_head]; exact PAll_bok
  have hc : chainOK (PrimData0.s0 :: PAll.tail) = true := by rw [← PAll_head]; exact PAll_chain
  have hp : ∀ x ∈ PrimData0.s0 :: PAll.tail, 20000000 + 1 < x.L + 2 * x.W → primOK (LLo 68 - LHi 25) x = true := by
    rw [← PAll_head]; intro x hx h; exact PAll_prim x hx (by omega)
  exact primorial_range_of 20000000 24000000 PrimData0.s0 PAll.tail PAll_s0 hc hok hp PAll_end cpos (by norm_num) n hn hn'
