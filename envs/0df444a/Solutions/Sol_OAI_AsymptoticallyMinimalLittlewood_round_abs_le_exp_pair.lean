-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.round_abs_le_exp_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:19:26.520145+00:00
-- url     : https://prove2.me/submissions/235df7fb-9e87-4065-a367-401afce91522

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L69-L107
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.round_abs_le_exp_pair. The node keeps its source
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

/-- A pointwise bound for the cost of quantizing a row sum. -/
theorem round_abs_le_exp_pair {x d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (htd : 4 ≤ t * d) :
    |(round (x / d) : ℝ)| ≤
      Real.exp (t * x - t * d / 4) + Real.exp (-t * x - t * d / 4) := by
  by_cases hq : round (x / d) = 0
  · rw [hq, Int.cast_zero, abs_zero]
    positivity
  have hq1 : (1 : ℝ) ≤ |(round (x / d) : ℝ)| := by
    have hi : (1 : ℤ) ≤ |round (x / d)| := by
      have := abs_pos.mpr hq
      omega
    exact_mod_cast hi
  have hbound : |(round (x / d) : ℝ)| ≤ |x| / d + 1 / 2 := by
    calc
      _ ≤ |x / d| + |x / d - (round (x / d) : ℝ)| := by
        have h := abs_add_le (x / d) (-(x / d - (round (x / d) : ℝ)))
        simp only [abs_neg] at h
        convert h using 1; congr 1; ring
      _ ≤ _ := by
        rw [abs_div, abs_of_pos hd]
        gcongr
        exact abs_sub_round (x / d)
  have hxd : (|(round (x / d) : ℝ)| - 1 / 2) * d ≤ |x| := by
    have := (le_div_iff₀ hd).mp (by linarith :
      |(round (x / d) : ℝ)| - 1 / 2 ≤ |x| / d)
    exact this
  have hcost : |(round (x / d) : ℝ)| ≤ t * |x| - t * d / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hxd ht
    have hprod := mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr htd)
    nlinarith
  have hxexp : |(round (x / d) : ℝ)| ≤ Real.exp (t * |x| - t * d / 4) := by
    nlinarith [Real.add_one_le_exp (t * |x| - t * d / 4)]
  apply hxexp.trans
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.round_abs_le_exp_pair := @_root_.OAI.AsymptoticallyMinimalLittlewood.round_abs_le_exp_pair
