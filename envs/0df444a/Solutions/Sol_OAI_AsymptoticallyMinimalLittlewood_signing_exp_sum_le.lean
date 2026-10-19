-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.signing_exp_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:17:47.64165+00:00
-- url     : https://prove2.me/submissions/01eeccef-315d-4d44-9a19-57846714d9ab

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L42-L67
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.signing_exp_sum_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_bool_exp_sum_le

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- MGF bound for all signings of a bounded real row, with counting measure. -/
theorem signing_exp_sum_le {α : Type u} [Fintype α] [DecidableEq α] (a : α → ℝ)
    (ha : ∀ k, |a k| ≤ 1) (t : ℝ) :
    (∑ x : α → Bool, Real.exp (t * ∑ k, a k * boolSign (x k))) ≤
      2 ^ Fintype.card α * Real.exp (t ^ 2 * Fintype.card α / 2) := by
  classical
  calc
    _ = ∏ k : α, ∑ b : Bool, Real.exp (t * a k * boolSign b) := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∏ _k : α, 2 * Real.exp (t ^ 2 / 2) := by
      apply Finset.prod_le_prod₀
      · intro k hk; positivity
      · intro k hk; exact bool_exp_sum_le (ha k) t
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, mul_pow]
      rw [← Real.exp_nat_mul]
      congr 2
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


theorem solution.{u} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.signing_exp_sum_le.{u} := @_root_.OAI.AsymptoticallyMinimalLittlewood.signing_exp_sum_le.{u}
