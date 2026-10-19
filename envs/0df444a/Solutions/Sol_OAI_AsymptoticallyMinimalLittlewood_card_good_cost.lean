-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.card_good_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:33:52.772995+00:00
-- url     : https://prove2.me/submissions/b8d9d2e0-d984-4a1b-8b7c-14567c4b46b0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L278-L299
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.card_good_cost. The node keeps its source
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

/-- A nonnegative cost with small average is small on at least half a finite set. -/
theorem card_good_cost {γ : Type w} [Fintype γ] [DecidableEq γ]
    (f : γ → ℝ) (hf : ∀ x, 0 ≤ f x) {M : ℝ} (hM : 0 < M)
    (hsum : (∑ x, f x) ≤ (Fintype.card γ : ℝ) * M / 2) :
    (Fintype.card γ : ℝ) / 2 ≤ ((Finset.univ.filter fun x ↦ f x ≤ M).card : ℝ) := by
  classical
  let G := Finset.univ.filter fun x ↦ f x ≤ M
  let B := Finset.univ.filter fun x ↦ ¬ f x ≤ M
  have hcard : G.card + B.card = Fintype.card γ := by
    exact Finset.card_filter_add_card_filter_not _
  have hlow : (B.card : ℝ) * M ≤ ∑ x, f x := by
    calc
      _ = ∑ _x ∈ B, M := by simp
      _ ≤ ∑ x ∈ B, f x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ ↦ hf x)
  have hc : (G.card : ℝ) + (B.card : ℝ) = Fintype.card γ := by exact_mod_cast hcard
  change _ ≤ (G.card : ℝ)
  nlinarith

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{w} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.card_good_cost.{w} := @_root_.OAI.AsymptoticallyMinimalLittlewood.card_good_cost.{w}
