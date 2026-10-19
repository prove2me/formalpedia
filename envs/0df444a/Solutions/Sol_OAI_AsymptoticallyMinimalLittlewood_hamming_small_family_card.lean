-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.hamming_small_family_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:32:17.906872+00:00
-- url     : https://prove2.me/submissions/f01c3235-c9d0-440a-80ab-0f2f8527239f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L236-L276
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.hamming_small_family_card. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_hamming_exp_sum

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- A small Hamming ball occupies exponentially less than the whole cube. -/
theorem hamming_small_family_card {α : Type u} [Fintype α] [DecidableEq α]
    (G : Finset (α → Bool)) (x : α → Bool)
    (hG : ∀ y ∈ G, (hammingDist x y : ℝ) ≤ (Fintype.card α : ℝ) / 16) :
    (G.card : ℝ) ≤ Real.exp (3 * Fintype.card α / 8) := by
  have he2 : Real.exp (-2) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    have h2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; norm_num at this; exact this
    have hh := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) h2
    rw [← Real.exp_add] at hh
    norm_num at hh ⊢
    exact hh
  have hsum : (∑ y : α → Bool, Real.exp (-2 * hammingDist x y)) ≤
      Real.exp (Fintype.card α / 4) := by
    rw [hamming_exp_sum]
    calc
      _ ≤ Real.exp (1 / 4) ^ Fintype.card α := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (1 / 4)]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlow : (G.card : ℝ) * Real.exp (-(Fintype.card α : ℝ) / 8) ≤
      ∑ y : α → Bool, Real.exp (-2 * hammingDist x y) := by
    calc
      _ = ∑ _y ∈ G, Real.exp (-(Fintype.card α : ℝ) / 8) := by simp
      _ ≤ ∑ y ∈ G, Real.exp (-2 * hammingDist x y) := by
        apply Finset.sum_le_sum
        intro y hy
        apply Real.exp_le_exp.mpr
        have := hG y hy
        linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ (Real.exp_pos _).le)
  have h := mul_le_mul_of_nonneg_left (hlow.trans hsum)
    (Real.exp_pos ((Fintype.card α : ℝ) / 8)).le
  have heq : (Fintype.card α : ℝ) / 8 + -(Fintype.card α : ℝ) / 8 = 0 := by ring
  rw [← mul_assoc, mul_comm (Real.exp _) (G.card : ℝ), mul_assoc, ← Real.exp_add,
    heq, Real.exp_zero, mul_one, ← Real.exp_add] at h
  convert h using 1
  congr 1
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


theorem solution.{u} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.hamming_small_family_card.{u} := @_root_.OAI.AsymptoticallyMinimalLittlewood.hamming_small_family_card.{u}
