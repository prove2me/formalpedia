-- Prove2me | solution 1 for OAI.DiamondDistortion.FiniteAverage.pooled_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:14:36.460961+00:00
-- url     : https://prove2.me/submissions/5a26a4e1-2e14-46be-a132-95e1f7e9461b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/FiniteAverage.lean:L69-L125
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.FiniteAverage.pooled_mass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Theorems.Thm_OAI_DiamondDistortion_FiniteAverage_jensen_sq

-- ---- from OAI.Analysis.DiamondDistortion.FiniteAverage ----
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace FiniteAverage
variable {Ω : Type*} [Fintype Ω]

lemma double_product (w f g : Ω → ℝ) :
    (∑ ω, w ω * f ω) * (∑ ω, w ω * g ω) =
      ∑ ω, ∑ ν, w ω * w ν * (f ω * g ν) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

/-- Averaged opposite-sign cancellation, including the error's gate energy. -/
lemma pooled_mass {κ : Type*} [Fintype κ]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω,w ω = 1)
    (b W : Ω → κ → ℝ) (V L : Ω → ℝ)
    (hmean : ∀ g, (∑ ω,w ω*b ω g) = -(∑ ω,w ω*W ω g))
    (hW : ∀ ω, (∑ g,W ω g ^ 2) ≤ V ω)
    (hopp : ∀ ω ν, (∑ g, (|b ω g| * |b ν g| - b ω g*b ν g)) ≤ L ω + L ν) :
    (∑ g, (∑ ω,w ω* |b ω g|)^2) ≤ (∑ ω,w ω*V ω) + 2*(∑ ω,w ω*L ω) := by
  have hsign : (∑ g, (∑ ω,w ω*b ω g)^2) ≤ ∑ ω,w ω*V ω := by
    calc
      _ ≤ ∑ g, ∑ ω,w ω*(W ω g)^2 := by
        apply Finset.sum_le_sum
        intro g _
        rw [hmean g, neg_sq]
        exact jensen_sq w (fun ω => W ω g) hw hs
      _ = ∑ ω,w ω*(∑ g,W ω g^2) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hW ω) (hw ω)
  have hleft : (∑ g, ((∑ ω,w ω* |b ω g|)^2 - (∑ ω,w ω*b ω g)^2)) =
      ∑ ω,∑ ν,w ω*w ν*(∑ g,(|b ω g| * |b ν g| - b ω g*b ν g)) := by
    calc
      _ = ∑ g, ∑ ω,∑ ν,w ω*w ν*(|b ω g| * |b ν g| - b ω g*b ν g) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [sq, sq, double_product, double_product, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ν _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ω _
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
  have hright : (∑ ω,∑ ν,w ω*w ν*(L ω+L ν)) = 2*(∑ ω,w ω*L ω) := by
    calc
      _ = (∑ ω,w ω*L ω)*(∑ ν,w ν) + (∑ ω,w ω)*(∑ ν,w ν*L ν) := by
        simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        apply Finset.sum_congr rfl
        intro ν _
        ring
      _ = _ := by rw [hs]; ring
  have hcross : (∑ ω,∑ ν,w ω*w ν*(∑ g,(|b ω g| * |b ν g| - b ω g*b ν g))) ≤
      ∑ ω,∑ ν,w ω*w ν*(L ω+L ν) := by
    apply Finset.sum_le_sum
    intro ω _
    apply Finset.sum_le_sum
    intro ν _
    exact mul_le_mul_of_nonneg_left (hopp ω ν) (mul_nonneg (hw ω) (hw ν))
  rw [← hleft, hright, Finset.sum_sub_distrib] at hcross
  linarith

end FiniteAverage

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.FiniteAverage
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.FiniteAverage.pooled_mass := @_root_.OAI.DiamondDistortion.FiniteAverage.pooled_mass
