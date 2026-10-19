-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.exists_partial_coloring
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:41:44.70599+00:00
-- url     : https://prove2.me/submissions/946d2cbc-3cd1-434e-944d-1d20fd48f562

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L513-L592
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.exists_partial_coloring. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_entropy_log_parameters
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_exists_signings_same_round

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- A zero-start partial coloring fixes a fixed positive fraction of all coordinates. -/
theorem exists_partial_coloring {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hs : 0 < Fintype.card α)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ z : α → ℝ, (∀ k, z k = -1 ∨ z k = 0 ∨ z k = 1) ∧
      (Fintype.card α : ℝ) / 16 ≤ ((Finset.univ.filter fun k ↦ z k ≠ 0).card : ℝ) ∧
      ∀ i, |∑ k, B i k * z k| ≤ 64 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (16 * Fintype.card β / Fintype.card α)) := by
  classical
  let s : ℝ := Fintype.card α
  let L := Real.log (16 * Fintype.card β / s)
  have hs0 : 0 < s := by dsimp [s]; exact_mod_cast hs
  have hsR' : s ≤ (Fintype.card β : ℝ) := by dsimp [s]; exact_mod_cast hsR
  have hL := (entropy_log_parameters hs0 hsR').1
  change 1 / 2 ≤ L at hL
  have hL0 : 0 < L := by linarith
  by_cases hn : 32 ≤ Fintype.card α
  · obtain ⟨x, y, hfar, heq⟩ := exists_signings_same_round B hB hn hsR
    let z : α → ℝ := fun k ↦ (boolSign (x k) - boolSign (y k)) / 2
    let d := 64 * Real.sqrt (s * L)
    have hd : 0 < d := by dsimp [d]; positivity
    have hz (k : α) : z k = -1 ∨ z k = 0 ∨ z k = 1 := by
      dsimp [z]
      cases x k <;> cases y k <;> norm_num [boolSign]
    have hcard : (Finset.univ.filter fun k ↦ z k ≠ 0).card = hammingDist x y := by
      unfold hammingDist
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [z]
      cases x k <;> cases y k <;> norm_num [boolSign]
    refine ⟨z, hz, ?_, ?_⟩
    · rw [hcard]
      exact hfar.le
    · intro i
      let u := ∑ k, B i k * boolSign (x k)
      let v := ∑ k, B i k * boolSign (y k)
      have hq : round (u / d) = round (v / d) := heq i
      have hdiff : |u / d - v / d| ≤ 1 := by
        calc
          _ = |(u / d - (round (u / d) : ℝ)) + ((round (u / d) : ℝ) - v / d)| := by
            congr 1
            ring
          _ ≤ |u / d - (round (u / d) : ℝ)| + |(round (u / d) : ℝ) - v / d| := abs_add_le _ _
          _ ≤ 1 := by
            rw [hq, abs_sub_comm (round (v / d) : ℝ)]
            have hu := abs_sub_round (u / d)
            rw [hq] at hu
            linarith [abs_sub_round (v / d)]
      have huv : |u - v| ≤ d := by
        rw [← sub_div, abs_div, abs_of_pos hd] at hdiff
        have := (div_le_iff₀ hd).mp hdiff
        linarith
      change _ ≤ d
      calc
        _ = |(u - v) / 2| := by
          congr 1
          dsimp [u, v, z]
          simp only [← mul_div_assoc, mul_sub]
          rw [← Finset.sum_div, Finset.sum_sub_distrib]
        _ = |u - v| / 2 := by rw [abs_div]; norm_num
        _ ≤ d / 2 := by gcongr
        _ ≤ d := by linarith
  · refine ⟨fun _ ↦ 1, fun _ ↦ Or.inr (Or.inr rfl), ?_, ?_⟩
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, Finset.filter_true,
        Finset.card_univ]
      nlinarith [(Nat.cast_nonneg (Fintype.card α) : (0 : ℝ) ≤ Fintype.card α)]
    · intro i
      have hsum : |∑ k, B i k * (1 : ℝ)| ≤ s := by
        calc
          _ ≤ ∑ k, |B i k * (1 : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k : α, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ by simpa using hB i k
          _ = s := by simp [s]
      apply hsum.trans
      change s ≤ 64 * Real.sqrt (s * L)
      have hs32 : s ≤ 32 := by dsimp [s]; exact_mod_cast (by omega : Fintype.card α ≤ 32)
      have hq : (Real.sqrt (s * L)) ^ 2 = s * L := Real.sq_sqrt (by positivity)
      have hp := Real.sqrt_nonneg (s * L)
      nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hs32), mul_le_mul_of_nonneg_left hL hs0.le]

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{u,v} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.exists_partial_coloring.{u,v} := @_root_.OAI.AsymptoticallyMinimalLittlewood.exists_partial_coloring.{u,v}
