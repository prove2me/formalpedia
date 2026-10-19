-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.dyadic_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:47:54.309954+00:00
-- url     : https://prove2.me/submissions/0abc9e71-13b6-4bef-aaad-eff7d50e20f0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L771-L816
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.dyadic_potential_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- The small mass controls the discrepancy potential at every dyadic scale. -/
theorem dyadic_potential_bound {s μ R : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ R)
    (hs : 0 ≤ s) (j : ℕ) (hsmass : s ≤ 2 ^ j * μ) :
    Real.sqrt (s * Real.log (2 * R / s)) / 2 ^ j ≤
      (3 / 4) ^ j * Real.sqrt (μ * Real.log (2 * R / μ)) := by
  have hR : 0 < R := by linarith
  have hratio : (4 : ℝ) ≤ 2 * R / μ := (le_div_iff₀ hμ).mpr (by linarith)
  let L := Real.log (2 * R / μ)
  have hL : 1 ≤ L := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hratio
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h4
    norm_num at h2 h4
    dsimp [L]
    linarith
  have hφ : 0 ≤ μ * L := mul_nonneg hμ.le (by linarith)
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hf : s * Real.log (2 * R / s) ≤ 2 ^ j * (μ * L) := by
    by_cases hz : s = 0
    · rw [hz, zero_mul]
      positivity
    have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hid : 2 * R / s = (2 * R / μ) * (μ / s) := by field_simp
    rw [hid, Real.log_mul (by positivity : 2 * R / μ ≠ 0)
      (by positivity : μ / s ≠ 0), mul_add]
    have hlog := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (show 0 < μ / s by positivity)) hs
    have heq : s * (μ / s - 1) = μ - s := by field_simp
    rw [heq] at hlog
    have hmult := mul_le_mul_of_nonneg_right hsmass (show 0 ≤ L - 1 by linarith)
    change s * L + s * Real.log (μ / s) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hpow hμ.le]
  have hscale : (2 : ℝ) ^ j ≤ ((3 / 4) ^ j * 2 ^ j) ^ 2 := by
    calc
      (2 : ℝ) ^ j ≤ (9 / 4) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
      _ = _ := by rw [← mul_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hroot := Real.sq_sqrt hφ
  change s * Real.log (2 * R / s) ≤ ((3 / 4) ^ j * Real.sqrt (μ * L) * 2 ^ j) ^ 2
  calc
    _ ≤ 2 ^ j * (μ * L) := hf
    _ ≤ (((3 / 4) ^ j * 2 ^ j) ^ 2) * (μ * L) := mul_le_mul_of_nonneg_right hscale hφ
    _ = _ := by calc
      _ = ((3 / 4) ^ j * 2 ^ j) ^ 2 * (Real.sqrt (μ * L)) ^ 2 := by rw [hroot]
      _ = _ := by ring

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.dyadic_potential_bound := @_root_.OAI.AsymptoticallyMinimalLittlewood.dyadic_potential_bound
