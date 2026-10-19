-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteDistribution.tv_maps_le_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:22:46.186399+00:00
-- url     : https://prove2.me/submissions/b7fa728c-b3c2-4867-87f3-7f0736c0324f

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteDistribution
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable
theorem h44_mapw {α : Type*} {β : Type*} (p : FiniteDistribution α) (f : α → β) (b : β) :
    (p.map f).weight b = ∑ a ∈ p.support, if f a = b then p.weight a else 0 := by
  unfold FiniteDistribution.map FiniteEntropy.mass
  dsimp only
  rw [Finset.sum_filter]

theorem solution {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f g : α → β) :
    (p.map f).tv (p.map g) ≤ ∑ a ∈ p.support, if f a = g a then 0 else p.weight a := by
  set T := p.support.image f ∪ p.support.image g with hT
  unfold tv
  have hz : ∀ b ∉ T, |(p.map f).weight b - (p.map g).weight b| = 0 := by
    intro b hb
    simp only [hT, Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hb
    rw [h44_mapw, h44_mapw, Finset.sum_eq_zero (fun a ha => if_neg (hb.1 a ha)),
      Finset.sum_eq_zero (fun a ha => if_neg (hb.2 a ha)), sub_self, abs_zero]
  rw [tsum_eq_sum (s := T) hz, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  calc ∑ b ∈ T, |(p.map f).weight b - (p.map g).weight b|
      ≤ ∑ b ∈ T, ∑ a ∈ p.support, (if f a = g a then 0 else
          ((if f a = b then p.weight a else 0) + (if g a = b then p.weight a else 0))) := by
        apply Finset.sum_le_sum
        intro b _
        rw [h44_mapw, h44_mapw, ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        by_cases h : f a = g a
        · rw [if_pos h, h, sub_self, abs_zero]
        · rw [if_neg h]
          have h1 : 0 ≤ (if f a = b then p.weight a else 0) := by
            split_ifs <;> simp [p.nonneg a]
          have h2 : 0 ≤ (if g a = b then p.weight a else 0) := by
            split_ifs <;> simp [p.nonneg a]
          rw [abs_le]; constructor <;> linarith
    _ = ∑ a ∈ p.support, (if f a = g a then 0 else p.weight a) * 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : f a = g a
        · simp [h]
        · simp only [if_neg h]
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
            if_pos (Finset.mem_union_left _ (Finset.mem_image_of_mem f ha)),
            if_pos (Finset.mem_union_right _ (Finset.mem_image_of_mem g ha))]
          ring
    _ = _ := by rw [Finset.sum_mul]

