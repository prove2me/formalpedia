-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.dyadic_round
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:51:14.2871+00:00
-- url     : https://prove2.me/submissions/1477e360-3ecf-4040-b570-26fc975e2f76

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L927-L966
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.dyadic_round. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_dyadic_round_step

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- Iteration of the dyadic steps. The mass bound is maintained, not reset at each scale. -/
theorem dyadic_round {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β) (j : ℕ) :
    ∀ a : α → ℕ, (∀ k, a k ≤ 2 ^ j) →
      (∑ k, (a k : ℝ) / 2 ^ j) ≤ μ →
      ∃ b : α → ℕ, (∀ k, b k ≤ 1) ∧
        (∑ k, (b k : ℝ)) ≤ (∑ k, (a k : ℝ) / 2 ^ j) ∧
        ∀ i, |∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)| ≤
          8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) := by
  induction j with
  | zero =>
    intro a ha hmass
    refine ⟨a, by simpa using ha, by simp, ?_⟩
    intro i
    simp
  | succ j ih =>
    intro a ha hmass
    obtain ⟨b, hb, hmassb, herrb⟩ := dyadic_round_step A hA hαβ a j ha hμ hμR hmass
    obtain ⟨c, hc, hmassc, herrc⟩ := ih b hb (hmassb.trans hmass)
    refine ⟨c, hc, hmassc.trans hmassb, fun i ↦ ?_⟩
    have hsplit : (∑ k, A i k * ((c k : ℝ) - (a k : ℝ) / 2 ^ (j + 1))) =
        (∑ k, A i k * ((c k : ℝ) - (b k : ℝ) / 2 ^ j)) +
        ∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hsplit]
    calc
      _ ≤ |∑ k, A i k * ((c k : ℝ) - (b k : ℝ) / 2 ^ j)| +
          |∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))| := abs_add_le _ _
      _ ≤ 8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) +
          8192 * ((3 / 4) ^ (j + 1) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) := add_le_add (herrc i) (herrb i)
      _ = _ := by rw [pow_succ]; ring

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{u,v} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.dyadic_round.{u,v} := @_root_.OAI.AsymptoticallyMinimalLittlewood.dyadic_round.{u,v}
