-- Prove2me | solution 1 for OAI.FixedClauseThreshold.replacement_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:22:03.689434+00:00
-- url     : https://prove2.me/submissions/d883c63e-9653-4712-b339-f7be3bd89eb7

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Replacement.lean:L228-L280
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.replacement_numeric. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Theorems.Thm_OAI_FixedClauseThreshold_killFraction_le_pow
import Theorems.Thm_OAI_FixedClauseThreshold_killFraction_succ

-- ---- from OAI.Probability.RandomSAT.Replacement ----
namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem killFraction_nonneg (b n r : ℕ) : 0 ≤ killFraction b n r := by
  unfold killFraction
  positivity

theorem killFraction_le_half_pow {b n r : ℕ} (hbn : b ≤ n) (hrn : r ≤ n)
    (hn : 0 < n) : killFraction b n r ≤ (1 / 2 : ℝ) ^ r := by
  apply (killFraction_le_pow hbn hrn hn).trans
  apply pow_le_pow_left₀ (by positivity)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  have hbn' : (b : ℝ) ≤ n := by exact_mod_cast hbn
  linarith

theorem nat_le_internal_choose {n r : ℕ} (hr : 1 ≤ r) (hrn : r < n) :
    n ≤ n.choose r := by
  induction n generalizing r with
  | zero => omega
  | succ n ih =>
    cases r with
    | zero => omega
    | succ r =>
      by_cases h : r = 0
      · subst r
        simp
      · rw [Nat.choose_succ_succ]
        have hlow := ih (by omega : 1 ≤ r) (by omega : r < n)
        have hpos := Nat.choose_pos (by omega : r.succ ≤ n)
        omega

theorem killFraction_small_forcing {b n r : ℕ} (hr : 1 ≤ r) (hrn : r < n)
    (hbr : b ≤ r) : killFraction b n r ≤ 1 / (n + 1 : ℝ) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnc : (n : ℝ) ≤ n.choose r := by exact_mod_cast nat_le_internal_choose hr hrn
  have hb : (b.choose r : ℝ) ≤ 1 := by
    exact_mod_cast (Nat.choose_le_choose r hbr).trans_eq (Nat.choose_self r)
  have hp : (2 : ℝ) ≤ 2 ^ r := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
  have hncpos : (0 : ℝ) < n.choose r := by linarith
  have hden : (0 : ℝ) < (n.choose r : ℝ) * 2 ^ r := by positivity
  unfold killFraction
  apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < n + 1)).mpr
  nlinarith [mul_le_mul hnc hp (by positivity : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ n.choose r)]

theorem succ_ratio_lower {b n r : ℕ} (hrb : r + 1 ≤ b) (hrn : r < n) :
    (b : ℝ) / (2 * n * (r + 1)) ≤
      ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr : (0 : ℝ) < (n - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hrn
  have hrb' : (r + 1 : ℝ) ≤ b := by exact_mod_cast hrb
  have hr : (0 : ℝ) ≤ r := by positivity
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n * (r + 1))
    (by positivity : (0 : ℝ) < 2 * (n - r : ℕ))]
  rw [Nat.cast_sub (by omega : r ≤ b), Nat.cast_sub (Nat.le_of_lt hrn)]
  have haux : (b : ℝ) ≤ (b - r) * (r + 1) := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrb')]
  nlinarith [mul_le_mul_of_nonneg_right haux hn.le,
    mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) hr]

theorem killFraction_succ_lower {b n r : ℕ} (hrb : r + 1 ≤ b) (hrn : r < n) :
    killFraction b n r * ((b : ℝ) / (2 * n)) / (r + 1) ≤
      killFraction b n (r + 1) := by
  rw [killFraction_succ (by omega : r + 1 ≤ n)]
  have h := mul_le_mul_of_nonneg_left (succ_ratio_lower hrb hrn)
    (killFraction_nonneg b n r)
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

theorem power_survival_bound {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) (g : ℕ) :
    (1 - q) ^ g * (1 + (g : ℝ) * q) ≤ 1 := by
  induction g with
  | zero => simp
  | succ g ih =>
    have hstep : (1 - q) * (1 + ((g : ℝ) + 1) * q) ≤ 1 + (g : ℝ) * q := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ g + 1) (sq_nonneg q)]
    calc
      (1 - q) ^ (g + 1) * (1 + ((g + 1 : ℕ) : ℝ) * q) =
          (1 - q) ^ g * ((1 - q) * (1 + ((g : ℝ) + 1) * q)) := by
            push_cast
            ring
      _ ≤ (1 - q) ^ g * (1 + (g : ℝ) * q) :=
        mul_le_mul_of_nonneg_left hstep (pow_nonneg (sub_nonneg.mpr hq1) _)
      _ ≤ 1 := ih

theorem block_ge_of_double {x q : ℝ} {g : ℕ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hg : 2 * x ≤ (g : ℝ) * q) : x ≤ 1 - (1 - q) ^ g := by
  have h := power_survival_bound hq0 hq1 g
  have hx1 : 0 ≤ 1 - x := by linarith
  have hg0 : 0 ≤ (g : ℝ) * q := by positivity
  have hh : 1 ≤ (1 - x) * (1 + (g : ℝ) * q) := by
    nlinarith [mul_le_mul_of_nonneg_right hg hx1, mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]
  have hb : (1 - q) ^ g ≤ 1 - x := by
    exact (mul_le_mul_iff_left₀ (by positivity : 0 < 1 + (g : ℝ) * q)).mp
      (by nlinarith)
  linarith

theorem replacement_numeric {b v r g : ℕ} {a : ℝ}
    (hr : 1 ≤ r) (hrv : r < v) (hbv : b ≤ v) (ha : 0 < a)
    (hsmall : 1 / (v + 1 : ℝ) ≤ a⁻¹ ^ r)
    (hg : 2 * (r + 1 : ℝ) * a ≤ (g : ℝ)) :
    killFraction b v r - a⁻¹ ^ r ≤ 1 - (1 - killFraction b v (r + 1)) ^ g := by
  let x := killFraction b v r
  let q := killFraction b v (r + 1)
  have hv : 0 < v := by omega
  have hx0 : 0 ≤ x := killFraction_nonneg _ _ _
  have hq0 : 0 ≤ q := killFraction_nonneg _ _ _
  have hxhalf : x ≤ 1 / 2 := by
    apply (killFraction_le_half_pow hbv (Nat.le_of_lt hrv) hv).trans
    calc
      (1 / 2 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
      _ = 1 / 2 := by simp
  have hq1 : q ≤ 1 := by
    apply (killFraction_le_half_pow hbv (by omega) hv).trans
    exact pow_le_one₀ (by norm_num) (by norm_num)
  by_cases hx : x ≤ a⁻¹ ^ r
  · have hpow : (1 - q) ^ g ≤ 1 :=
      pow_le_one₀ (sub_nonneg.mpr hq1) (by linarith)
    change x - a⁻¹ ^ r ≤ 1 - (1 - q) ^ g
    linarith
  · have hrb : r + 1 ≤ b := by
      by_contra h
      have hb : b ≤ r := by omega
      have hbound := killFraction_small_forcing hr hrv hb
      exact hx (hbound.trans hsmall)
    have ht : a⁻¹ ≤ (b : ℝ) / (2 * v) := by
      by_contra h
      have hle : (b : ℝ) / (2 * v) ≤ a⁻¹ := (lt_of_not_ge h).le
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (b : ℝ) / (2 * v)) hle r
      have hbound := killFraction_le_pow hbv (Nat.le_of_lt hrv) hv
      exact hx (hbound.trans hpow)
    have hat : 1 ≤ a * ((b : ℝ) / (2 * v)) := by
      simpa [ne_of_gt ha] using mul_le_mul_of_nonneg_left ht ha.le
    have hqlo := killFraction_succ_lower hrb hrv
    have hprod : (2 * (r + 1 : ℝ) * a) *
        (x * ((b : ℝ) / (2 * v)) / (r + 1)) ≤ (g : ℝ) * q :=
      mul_le_mul hg hqlo (by positivity) (by positivity)
    have hrpos : (r + 1 : ℝ) ≠ 0 := by positivity
    have heq : (2 * (r + 1 : ℝ) * a) *
        (x * ((b : ℝ) / (2 * v)) / (r + 1)) =
        2 * x * (a * ((b : ℝ) / (2 * v))) := by
      field_simp
    rw [heq] at hprod
    have hdbl : 2 * x ≤ (g : ℝ) * q := by
      nlinarith [mul_le_mul_of_nonneg_left hat (by positivity : 0 ≤ 2 * x)]
    have hb := block_ge_of_double hx0 hxhalf hq0 hq1 hdbl
    have heps : 0 ≤ a⁻¹ ^ r := by positivity
    change x - a⁻¹ ^ r ≤ 1 - (1 - q) ^ g
    linarith

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.replacement_numeric := @_root_.OAI.FixedClauseThreshold.replacement_numeric
