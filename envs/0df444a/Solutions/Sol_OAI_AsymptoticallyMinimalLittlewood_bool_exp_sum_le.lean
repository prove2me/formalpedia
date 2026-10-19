-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.bool_exp_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:16:25.840678+00:00
-- url     : https://prove2.me/submissions/1313cb21-a392-435d-97a9-5cc29a2dd129

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L26-L40
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.bool_exp_sum_le. The node keeps its source
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

/-- Elementary Rademacher MGF bound for one bounded coefficient. -/
theorem bool_exp_sum_le {a : ℝ} (ha : |a| ≤ 1) (t : ℝ) :
    (∑ b : Bool, Real.exp (t * a * boolSign b)) ≤ 2 * Real.exp (t ^ 2 / 2) := by
  simp only [Fintype.sum_bool, boolSign, ite_true, Bool.false_eq_true,
    ite_false, mul_one, mul_neg_one]
  calc
    Real.exp (t * a) + Real.exp (-(t * a)) = 2 * Real.cosh (t * a) := by
      rw [Real.cosh_eq]; ring
    _ ≤ 2 * Real.exp ((t * a) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq _) (by norm_num)
    _ ≤ 2 * Real.exp (t ^ 2 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a]
      nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ha2)]

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.bool_exp_sum_le := @_root_.OAI.AsymptoticallyMinimalLittlewood.bool_exp_sum_le
