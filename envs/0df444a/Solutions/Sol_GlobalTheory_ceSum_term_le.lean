-- Prove2me | solution 1 for GlobalTheory.ceSum_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:06.46552+00:00
-- url     : https://prove2.me/submissions/53a77225-dd60-477f-af09-9f5249803399

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CmValuesExponentLogSumLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
open Formalism.PairingDivisionLocalBalance
namespace GlobalTheory
theorem _root_.solution (f X l : ℕ) (hX : X ≠ 0) (hp : l.Prime) :
    ((f * padicValNat l 2 + mE l X : ℕ) : ℝ) * Real.log l ≤
      (padicValNat l X : ℝ) * Real.log l + (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0)
        + (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
        + (if l ≤ X / 2 + 1 then Real.log l else 0) := by
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hv : (0 : ℝ) ≤ padicValNat l X := Nat.cast_nonneg _
  have hvl : 0 ≤ (padicValNat l X : ℝ) * Real.log l := mul_nonneg hv hlog
  have hB : 0 ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0) := by
    split_ifs
    · exact Real.log_nonneg (by have : (0 : ℝ) ≤ X := Nat.cast_nonneg _; linarith)
    · exact le_rfl
  have hC : 0 ≤ (if l ≤ X / 2 + 1 then Real.log l else 0) := by
    split_ifs
    · exact hlog
    · exact le_rfl
  by_cases h2 : l = 2
  · subst h2
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hm : mE 2 X = 2 + padicValNat 2 X := by simp [mE]
    have h22 : padicValNat 2 2 = 1 := by simp
    have e : ((f * padicValNat 2 2 + mE 2 X : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ)
        = (padicValNat 2 X : ℝ) * Real.log ((2 : ℕ) : ℝ) + ((f : ℝ) + 2) * Real.log 2 := by
      rw [hm, h22]; push_cast; ring
    rw [if_pos rfl, e]
    linarith
  · have hA : (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0) = 0 := if_neg h2
    have hv2 : padicValNat l 2 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    rw [hA, hv2]
    by_cases hd : (l - 1) ∣ X
    · have hm : mE l X = 1 + padicValNat l X := by simp [mE, h2, hd]
      rw [hm]
      push_cast
      have key : Real.log (l : ℝ) ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
          + (if l ≤ X / 2 + 1 then Real.log l else 0) := by
        by_cases hXl : l = X + 1
        · rw [if_pos hXl]
          have : (l : ℝ) = (X : ℝ) + 1 := by exact_mod_cast hXl
          have e : Real.log (l : ℝ) = Real.log ((X : ℝ) + 1) := by rw [this]
          linarith
        · rw [if_neg hXl]
          have hl3 : 3 ≤ l := by have := hp.two_le; omega
          obtain ⟨k, hk⟩ := hd
          have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hX hk
          have hk1 : k ≠ 1 := by rintro rfl; apply hXl; omega
          have hk2 : (l - 1) * 2 ≤ (l - 1) * k := Nat.mul_le_mul_left _ (by omega)
          have hle : l - 1 ≤ X / 2 := by
            rw [Nat.le_div_iff_mul_le (by norm_num)]
            rw [hk]; exact hk2
          rw [if_pos (by omega)]
          linarith
      nlinarith
    · have hm : mE l X = 0 := by simp [mE, h2, hd]
      rw [hm]
      simp only [mul_zero, add_zero, Nat.cast_zero, zero_mul]
      linarith
end GlobalTheory
