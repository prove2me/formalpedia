-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.signing_round_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:20:53.917985+00:00
-- url     : https://prove2.me/submissions/e1ffaaee-d7f8-4cb0-a5bd-99bb4e71e4d5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L109-L135
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.signing_round_sum_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_round_abs_le_exp_pair
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_signing_exp_sum_le

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- Counting-measure bound for the average quantization cost of a bounded row. -/
theorem signing_round_sum_le {α : Type u} [Fintype α] [DecidableEq α] (a : α → ℝ)
    (ha : ∀ k, |a k| ≤ 1) {d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (htd : 4 ≤ t * d) :
    (∑ x : α → Bool, |(round ((∑ k, a k * boolSign (x k)) / d) : ℝ)|) ≤
      2 ^ Fintype.card α * (2 * Real.exp (t ^ 2 * Fintype.card α / 2 - t * d / 4)) := by
  classical
  calc
    _ ≤ ∑ x : α → Bool,
        (Real.exp (t * (∑ k, a k * boolSign (x k)) - t * d / 4) +
        Real.exp (-t * (∑ k, a k * boolSign (x k)) - t * d / 4)) := by
      exact Finset.sum_le_sum fun x hx ↦ round_abs_le_exp_pair hd ht htd
    _ = (Real.exp (-(t * d / 4))) *
        ((∑ x : α → Bool, Real.exp (t * ∑ k, a k * boolSign (x k))) +
        (∑ x : α → Bool, Real.exp (-t * ∑ k, a k * boolSign (x k)))) := by
      simp_rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      ring
    _ ≤ Real.exp (-(t * d / 4)) *
        (2 ^ Fintype.card α * Real.exp (t ^ 2 * Fintype.card α / 2) +
        2 ^ Fintype.card α * Real.exp ((-t) ^ 2 * Fintype.card α / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (signing_exp_sum_le a ha t) (signing_exp_sum_le a ha (-t)))
        (Real.exp_pos _).le
    _ = _ := by
      simp only [neg_sq, Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
      ring

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{u} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.signing_round_sum_le.{u} := @_root_.OAI.AsymptoticallyMinimalLittlewood.signing_round_sum_le.{u}
