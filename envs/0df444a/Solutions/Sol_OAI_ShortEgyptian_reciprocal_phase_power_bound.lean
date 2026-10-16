-- Prove2me | solution 1 for OAI.ShortEgyptian.reciprocal_phase_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:33:38.466309+00:00
-- url     : https://prove2.me/submissions/255512b8-1163-4fb8-8aaf-e23b5082010e

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ParameterBounds.lean:L173-L210
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.reciprocal_phase_power_bound. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_reciprocal_phase_order

-- ---- from OAI.NumberTheory.ShortEgyptian.ParameterBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem reciprocalConstant_pos (r : ℕ) : 0 < reciprocalConstantNat r := by
  unfold reciprocalConstantNat
  positivity

theorem reciprocalConstant_mono : Monotone reciprocalConstantNat := by
  intro r s hrs
  unfold reciprocalConstantNat
  gcongr <;> norm_num

theorem reciprocalPower_mono : Monotone reciprocalPower := by
  intro r s hrs
  unfold reciprocalPower
  gcongr <;> norm_num

theorem reciprocal_phase_power_bound (B : ℕ) (T U Z : ℝ) (p q : ℤ)
    (hB : 4 ≤ B) (hT : 1 ≤ T)
    (hlarge : (reciprocalConstantNat B : ℝ) * T ^ reciprocalPower B ≤ U)
    (hZlo : U ^ 4 ≤ |Z|) (hZhi : |Z| ≤ U ^ B)
    (hp : U ≤ p) (hq : (q : ℝ) ≤ 2 * U) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 8 * U / T := by
  have hC : (1 : ℝ) ≤ reciprocalConstantNat B := by
    exact_mod_cast reciprocalConstant_pos B
  have hU : 1 ≤ U := le_trans (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hT)) hlarge
  have hlow : U ^ 8 ≤ |Z| ^ 2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ U ^ 4) hZlo 2
  have hhigh : |Z| ^ 2 ≤ U ^ (2 * B) := by
    simpa only [← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ (abs_nonneg Z) hZhi 2
  have hex : ∃ r : ℕ, 2 ≤ r ∧ |Z| ^ 2 ≤ U ^ (2 * r + 5) := by
    exact ⟨B, by omega, hhigh.trans (pow_le_pow_right₀ hU (by omega))⟩
  let r := Nat.find hex
  have hr := Nat.find_spec hex
  change 2 ≤ r ∧ |Z| ^ 2 ≤ U ^ (2 * r + 5) at hr
  have hrB : r ≤ B := Nat.find_min' hex ⟨by omega, hhigh.trans (pow_le_pow_right₀ hU (by omega))⟩
  have hrlo : U ^ (2 * r + 3) ≤ |Z| ^ 2 := by
    by_cases heq : r = 2
    · rw [heq]
      exact (pow_le_pow_right₀ hU (by norm_num : 2 * 2 + 3 ≤ 8)).trans hlow
    · have hprev := Nat.find_min hex (show r - 1 < r by omega)
      have hnot : ¬ |Z| ^ 2 ≤ U ^ (2 * (r - 1) + 5) := fun hh => hprev ⟨by omega, hh⟩
      have he : 2 * (r - 1) + 5 = 2 * r + 3 := by omega
      rw [he] at hnot
      exact (lt_of_not_ge hnot).le
  have hlarge' : (reciprocalConstantNat r : ℝ) * T ^ reciprocalPower r ≤ U := by
    apply le_trans _ hlarge
    gcongr
    · exact_mod_cast reciprocalConstant_mono hrB
    · exact reciprocalPower_mono hrB
  have hh := reciprocal_phase_order r T U |Z| p q hT hlarge' (abs_nonneg Z) hrlo hr.2 hp hq
  rcases le_total 0 Z with hZ | hZ
  · simpa only [abs_of_nonneg hZ] using hh
  · rw [abs_of_nonpos hZ] at hh
    simpa only [neg_div, phase_neg, ← map_sum, Complex.norm_conj] using hh

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.reciprocal_phase_power_bound := @_root_.OAI.ShortEgyptian.reciprocal_phase_power_bound
