-- Prove2me | solution 1 for OAI.ShortEgyptian.reciprocal_phase_order
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:30:38.276678+00:00
-- url     : https://prove2.me/submissions/75527414-887b-4a25-8cdb-c605129bbda1

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ParameterBounds.lean:L92-L161
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.reciprocal_phase_order. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_reciprocal_parameter_algebra
import Theorems.Thm_OAI_ShortEgyptian_reciprocal_phase_parameter_bound

-- ---- from OAI.NumberTheory.ShortEgyptian.ParameterBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem reciprocalConstant_pos (r : ℕ) : 0 < reciprocalConstantNat r := by
  unfold reciprocalConstantNat
  positivity

theorem reciprocal_phase_order (r : ℕ) (T U Z : ℝ) (p q : ℤ)
    (hT : 1 ≤ T) (hlarge : (reciprocalConstantNat r : ℝ) * T ^ reciprocalPower r ≤ U)
    (hZ : 0 ≤ Z) (hZlo : U ^ (2 * r + 3) ≤ Z ^ 2)
    (hZhi : Z ^ 2 ≤ U ^ (2 * r + 5))
    (hp : U ≤ p) (hq : (q : ℝ) ≤ 2 * U) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 8 * U / T := by
  let A : ℝ := 3 ^ (r + 3)
  let F : ℝ := (r + 2).factorial
  let v : ℝ := T ^ (2 ^ r)
  let L : ℕ := ⌈v⌉₊
  let b : ℝ := Z / U ^ (r + 3)
  have hT0 : 0 < T := by linarith
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hF : 1 ≤ F := by
    have h : 1 ≤ (r + 2).factorial := Nat.factorial_pos (r + 2)
    dsimp only [F]
    exact_mod_cast h
  have hv : 1 ≤ v := one_le_pow₀ hT
  have hv0 : 0 < v := by linarith
  have hC0 : (0 : ℝ) < reciprocalConstantNat r := by exact_mod_cast reciprocalConstant_pos r
  have hU : 0 < U := lt_of_lt_of_le (mul_pos hC0 (by positivity)) hlarge
  have hL : 1 ≤ L := Nat.ceil_pos.mpr hv0
  have hLv : (L : ℝ) ≤ 2 * v := by
    have hh := Nat.ceil_lt_add_one hv0.le
    change (⌈v⌉₊ : ℝ) ≤ _
    linarith
  have hbaseLow : 1 ≤ U ^ 3 * b ^ 2 := by
    have heq : U ^ 3 * b ^ 2 = Z ^ 2 / U ^ (2 * r + 3) := by
      dsimp only [b]
      rw [div_pow, ← pow_mul, show (r + 3) * 2 = 3 + (2 * r + 3) by omega, pow_add]
      field_simp
    rw [heq]
    exact (one_le_div (by positivity)).mpr hZlo
  have hbaseHigh : U * b ^ 2 ≤ 1 := by
    have heq : U * b ^ 2 = Z ^ 2 / U ^ (2 * r + 5) := by
      dsimp only [b]
      rw [div_pow, ← pow_mul, show (r + 3) * 2 = 1 + (2 * r + 5) by omega, pow_add, pow_one]
      field_simp
    rw [heq]
    exact (div_le_one (by positivity)).mpr hZhi
  have hlarge' : (18 * A) ^ 4 * F ^ 2 * (2 : ℝ) ^ (2 * r) * v ^ (2 * r + 4) ≤ U := by
    simpa only [A, F, v, ← pow_mul, reciprocalPower, reciprocalConstantNat,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hlarge
  obtain ⟨hU1, hlo, hup⟩ := reciprocal_parameter_algebra r A F U v b L
    hA hF hv hU (by dsimp [b]; positivity) (by positivity) hLv hlarge' hbaseLow hbaseHigh
  have hUone : 1 ≤ U := by nlinarith
  have hfunc : F * b / A = Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3)) := by
    dsimp only [F, b, A]
    rw [one_div_pow, mul_pow]
    field_simp
  have hepow : (1 / T) ^ (2 ^ r) = 1 / v := one_div_pow T (2 ^ r)
  have heps : 0 < (1 : ℝ) / T := by positivity
  have heps1 : (1 : ℝ) / T ≤ 1 := (div_le_one hT0).mpr hT
  have hLin : 1 / (L : ℝ) ≤ (1 / T) ^ (2 ^ r) := by
    rw [hepow]
    exact one_div_le_one_div_of_le hv0 (Nat.le_ceil v)
  have hconstant : 18 ≤ U * (1 / T) ^ (2 ^ r) := by
    rw [hepow, mul_one_div]
    exact (le_div_iff₀ hv0).mpr hU1
  have hlo' : (18 / (U * (1 / T) ^ (2 ^ r))) ^ 2 ≤
      Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3)) := by
    rw [← hfunc, hepow]
    convert hlo using 1; field_simp
  have hup' : (L : ℝ) ^ r * (Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3))) ≤
      ((1 / T) ^ (2 ^ r) / (18 * (3 : ℝ) ^ (r + 3))) ^ 2 := by
    rw [← hfunc, hepow]
    convert hup using 1; field_simp; rfl
  have hh := reciprocal_phase_parameter_bound r L Z U (1 / T) p q hL hUone
    (by nlinarith) hZ hp hq heps heps1 hLin hconstant hlo' hup'
  simpa only [mul_one_div] using hh

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.reciprocal_phase_order := @_root_.OAI.ShortEgyptian.reciprocal_phase_order
