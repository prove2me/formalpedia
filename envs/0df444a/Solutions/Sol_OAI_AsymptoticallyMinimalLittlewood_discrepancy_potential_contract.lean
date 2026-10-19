-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.discrepancy_potential_contract
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:43:28.631775+00:00
-- url     : https://prove2.me/submissions/8ee7efae-93f3-4a58-86df-89bf52bf44e3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L594-L636
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.discrepancy_potential_contract. The node keeps its source
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

/-- The logarithmic discrepancy potential contracts on shortening the remaining columns. -/
theorem discrepancy_potential_contract {s u R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hu0 : 0 ≤ u) (hu : u ≤ (15 / 16) * s) :
    Real.sqrt (u * Real.log (16 * R / u)) ≤
      (63 / 64) * Real.sqrt (s * Real.log (16 * R / s)) := by
  by_cases hu_eq : u = 0
  · rw [hu_eq]
    simp only [zero_mul, Real.sqrt_zero]
    positivity
  have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_eq)
  have hR : 0 < R := hs.trans_le hsR
  let L := Real.log (16 * R / s)
  have hratio : (16 : ℝ) ≤ 16 * R / s := (le_div_iff₀ hs).mpr (by nlinarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hL : 2 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hratio
    rw [hlog16] at hh
    change _ ≤ L at hh
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log (16 * R / u) = L + Real.log (s / u) := by
    have hid : 16 * R / u = (16 * R / s) * (s / u) := by field_simp
    rw [hid, Real.log_mul (by positivity : 16 * R / s ≠ 0) (by positivity : s / u ≠ 0)]
  have hsmall : u * Real.log (s / u) ≤ s - u := by
    calc
      _ ≤ u * (s / u - 1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (by positivity)) hu0
      _ = _ := by field_simp
  have hsq : u * Real.log (16 * R / u) ≤ (31 / 32) * (s * L) := by
    rw [hlog, mul_add]
    have hprod := mul_le_mul_of_nonneg_right hu (show 0 ≤ L - 1 by linarith)
    have hLs := mul_le_mul_of_nonneg_left hL hs.le
    nlinarith
  apply (Real.sqrt_le_left (by positivity : 0 ≤ (63 / 64) * Real.sqrt (s * L))).mpr
  have hsqrt := Real.sq_sqrt (mul_nonneg hs.le hL0)
  change u * Real.log (16 * R / u) ≤ ((63 / 64) * Real.sqrt (s * L)) ^ 2
  nlinarith [mul_nonneg hs.le hL0]

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.discrepancy_potential_contract := @_root_.OAI.AsymptoticallyMinimalLittlewood.discrepancy_potential_contract
