-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.code_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:26:36.380806+00:00
-- url     : https://prove2.me/submissions/dc6801ee-ef55-4556-a90f-3647ffef04e1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L199-L217
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.code_card_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_code_exp_sum_le

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- A cost bound controls the number of possible quantization codes. -/
theorem code_card_le {β : Type v} [Fintype β] [DecidableEq β]
    (C : Finset (β → ℤ)) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : Real.exp (-a) ≤ 1 / 2) (hM : ∀ c ∈ C, (∑ i, |(c i : ℝ)|) ≤ M) :
    (C.card : ℝ) ≤ Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a)) := by
  have hlow : (C.card : ℝ) * Real.exp (-a * M) ≤
      ∑ c ∈ C, Real.exp (-a * ∑ i, |(c i : ℝ)|) := by
    calc
      _ = ∑ _c ∈ C, Real.exp (-a * M) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro c hc
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hM c hc) (neg_nonpos.mpr ha0))
  have hfull := mul_le_mul_of_nonneg_left (hlow.trans (code_exp_sum_le C a ha))
    (Real.exp_pos (a * M)).le
  rw [← mul_assoc, mul_comm (Real.exp (a * M)) (C.card : ℝ), mul_assoc,
    ← Real.exp_add, show a * M + -a * M = 0 by ring, Real.exp_zero, mul_one,
    ← Real.exp_add] at hfull
  exact hfull

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{v} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.code_card_le.{v} := @_root_.OAI.AsymptoticallyMinimalLittlewood.code_card_le.{v}
