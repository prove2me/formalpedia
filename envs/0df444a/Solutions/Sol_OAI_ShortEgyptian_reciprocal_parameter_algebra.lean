-- Prove2me | solution 1 for OAI.ShortEgyptian.reciprocal_parameter_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:28:58.783668+00:00
-- url     : https://prove2.me/submissions/775e3966-204c-43c0-bcf0-39500dece7bf

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ParameterBounds.lean:L10-L81
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.reciprocal_parameter_algebra. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds

-- ---- from OAI.NumberTheory.ShortEgyptian.ParameterBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem reciprocal_parameter_algebra (r : ℕ) (A F U v b L : ℝ)
    (hA : 1 ≤ A) (hF : 1 ≤ F) (hv : 1 ≤ v) (hU : 0 < U)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hLv : L ≤ 2 * v)
    (hlarge : (18 * A) ^ 4 * F ^ 2 * (2 : ℝ) ^ (2 * r) * v ^ (2 * r + 4) ≤ U)
    (hbaseLow : 1 ≤ U ^ 3 * b ^ 2) (hbaseHigh : U * b ^ 2 ≤ 1) :
    18 * v ≤ U ∧ (18 * v / U) ^ 2 ≤ F * b / A ∧
      L ^ r * (F * b / A) ≤ (1 / (18 * A * v)) ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hv0 : 0 < v := by linarith
  have hcoef : (18 * A) ^ 4 ≤ (18 * A) ^ 4 * F ^ 2 * (2 : ℝ) ^ (2 * r) := by
    calc
      _ = (18 * A) ^ 4 * 1 * 1 := by ring
      _ ≤ _ := by
        gcongr
        · exact one_le_pow₀ hF
        · exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hU4 : (18 * A) ^ 4 * v ^ 4 ≤ U := by
    apply le_trans _ hlarge
    exact mul_le_mul hcoef (pow_le_pow_right₀ hv (by omega)) (by positivity) (by positivity)
  have h18 : 18 ≤ (18 * A) ^ 4 := by
    have hh := pow_le_pow_right₀ (show 1 ≤ 18 * A by linarith) (show 1 ≤ 4 by norm_num)
    simp only [pow_one] at hh
    linarith
  have hU1 : 18 * v ≤ U := by
    have hp : v ≤ v ^ 4 := by simpa only [pow_one] using pow_le_pow_right₀ hv (show 1 ≤ 4 by norm_num)
    exact (mul_le_mul h18 hp hv0.le (by positivity)).trans hU4
  refine ⟨hU1, ?_, ?_⟩
  · have hM : (18 * v) ^ 4 * A ^ 2 ≤ U := by
      have hAA := pow_le_pow_right₀ hA (show 2 ≤ 4 by norm_num)
      have hm := mul_le_mul_of_nonneg_left hAA (show 0 ≤ (18 * v) ^ 4 by positivity)
      have heq : (18 * v) ^ 4 * A ^ 4 = (18 * A) ^ 4 * v ^ 4 := by ring
      rw [heq] at hm
      exact hm.trans hU4
    have hsq1 : ((18 * v / U) ^ 2) ^ 2 ≤ 1 / (A ^ 2 * U ^ 3) := by
      rw [← pow_mul, show 2 * 2 = 4 by norm_num, div_pow]
      apply (div_le_div_iff₀ (by positivity : 0 < U ^ 4) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_right hM (show 0 ≤ U ^ 3 by positivity)
      nlinarith only [hh]
    have hsq2 : 1 / (A ^ 2 * U ^ 3) ≤ (b / A) ^ 2 := by
      rw [div_pow]
      have hb2 : 1 / U ^ 3 ≤ b ^ 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hbaseLow])
      calc
        _ = (1 / U ^ 3) / A ^ 2 := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hb2 (by positivity)
    have hh := (sq_le_sq₀ (sq_nonneg (18 * v / U)) (by positivity : 0 ≤ b / A)).mp (hsq1.trans hsq2)
    apply hh.trans
    have hh' := mul_le_mul_of_nonneg_right hF (show 0 ≤ b / A by positivity)
    simpa only [mul_div_assoc, one_mul] using hh'
  · have hc : F * b / A ≤ F * b := div_le_self (by positivity) hA
    have hterm : L ^ r * (F * b / A) ≤ (2 * v) ^ r * (F * b) :=
      mul_le_mul (pow_le_pow_left₀ hL hLv r) hc (by positivity) (by positivity)
    have hb2 : b ^ 2 ≤ 1 / U := (le_div_iff₀ hU).mpr (by nlinarith only [hbaseHigh])
    have hsq : (L ^ r * (F * b / A)) ^ 2 ≤ ((1 / (18 * A * v)) ^ 2) ^ 2 := by
      calc
        _ ≤ ((2 * v) ^ r * (F * b)) ^ 2 := pow_le_pow_left₀ (by positivity) hterm 2
        _ = ((2 : ℝ) ^ (2 * r) * v ^ (2 * r) * F ^ 2) * b ^ 2 := by
          simp only [mul_pow, ← pow_mul, Nat.mul_comm r 2]
          ring
        _ ≤ ((2 : ℝ) ^ (2 * r) * v ^ (2 * r) * F ^ 2) * (1 / U) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
        _ = ((2 : ℝ) ^ (2 * r) * v ^ (2 * r) * F ^ 2) / U := by ring
        _ ≤ 1 / (18 * A * v) ^ 4 := by
          apply (div_le_div_iff₀ hU (by positivity)).mpr
          calc
            _ = (18 * A) ^ 4 * F ^ 2 * (2 : ℝ) ^ (2 * r) * v ^ (2 * r + 4) := by
              rw [pow_add]
              ring
            _ ≤ U := hlarge
            _ = 1 * U := by ring
        _ = _ := by rw [← pow_mul, show 2 * 2 = 4 by norm_num, one_div_pow]
    exact (sq_le_sq₀ (by positivity) (sq_nonneg _)).mp hsq

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.reciprocal_parameter_algebra := @_root_.OAI.ShortEgyptian.reciprocal_parameter_algebra
