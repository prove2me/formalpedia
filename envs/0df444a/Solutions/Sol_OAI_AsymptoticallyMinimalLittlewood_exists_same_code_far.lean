-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.exists_same_code_far
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:35:41.798035+00:00
-- url     : https://prove2.me/submissions/18e45b8b-8e9a-43d8-b94b-c0a4d404d1d2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L301-L342
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.exists_same_code_far. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_code_card_le
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_hamming_small_family_card

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- A large set of Boolean vectors contains a far pair with the same low-cost code. -/
theorem exists_same_code_far {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (G : Finset (α → Bool))
    (code : (α → Bool) → β → ℤ) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : Real.exp (-a) ≤ 1 / 2)
    (hcost : ∀ x ∈ G, (∑ i, |(code x i : ℝ)|) ≤ M)
    (hlarge : Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a) +
      3 * Fintype.card α / 8) < (G.card : ℝ)) :
    ∃ x ∈ G, ∃ y ∈ G, code x = code y ∧
      (Fintype.card α : ℝ) / 16 < (hammingDist x y : ℝ) := by
  classical
  by_contra h
  have hnear : ∀ x ∈ G, ∀ y ∈ G, code x = code y →
      (hammingDist x y : ℝ) ≤ (Fintype.card α : ℝ) / 16 := by
    intro x hx y hy hxy
    by_contra! hn
    exact h ⟨x, hx, y, hy, hxy, hn⟩
  let C := G.image code
  have hC : (C.card : ℝ) ≤ Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a)) := by
    apply code_card_le C ha0 ha
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact hcost x hx
  have hfiber (c : β → ℤ) (hc : c ∈ C) :
      ((G.filter fun x ↦ code x = c).card : ℝ) ≤ Real.exp (3 * Fintype.card α / 8) := by
    obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp hc
    apply hamming_small_family_card _ x
    intro y hy
    obtain ⟨hy, hyc⟩ := Finset.mem_filter.mp hy
    exact hnear x hx y hy (hxc.trans hyc.symm)
  have htotal : (G.card : ℝ) ≤ (C.card : ℝ) * Real.exp (3 * Fintype.card α / 8) := by
    calc
      _ = ∑ c ∈ C, ((G.filter fun x ↦ code x = c).card : ℝ) := by
        simpa using (Finset.sum_fiberwise_of_maps_to
          (fun x hx ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩ : ∀ x ∈ G, code x ∈ C)
          (fun _ ↦ (1 : ℝ))).symm
      _ ≤ ∑ _c ∈ C, Real.exp (3 * Fintype.card α / 8) := Finset.sum_le_sum hfiber
      _ = _ := by simp
  have hbound := htotal.trans (mul_le_mul_of_nonneg_right hC
    (Real.exp_pos (3 * Fintype.card α / 8)).le)
  rw [← Real.exp_add] at hbound
  exact (not_lt_of_ge hbound) hlarge

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{u,v} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.exists_same_code_far.{u,v} := @_root_.OAI.AsymptoticallyMinimalLittlewood.exists_same_code_far.{u,v}
