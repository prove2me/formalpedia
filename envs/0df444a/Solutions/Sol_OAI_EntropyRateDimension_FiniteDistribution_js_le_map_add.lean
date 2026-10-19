-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteDistribution.js_le_map_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:27:46.943615+00:00
-- url     : https://prove2.me/submissions/f943baab-407d-4d4d-a44d-39b6b7764dde

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

theorem h44_mapwS {α : Type*} {β : Type*} (p : FiniteDistribution α) (f : α → β) (b : β)
    (S : Finset α) (hS : p.support ⊆ S) :
    (p.map f).weight b = ∑ a ∈ S, if f a = b then p.weight a else 0 := by
  rw [h44_mapw]
  apply Finset.sum_subset hS
  intro a _ ha
  rw [p.vanish a ha]
  simp

theorem h44_nml_sum {ι : Type*} (t : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ t, 0 ≤ x i) :
    Real.negMulLog (∑ i ∈ t, x i) ≤ ∑ i ∈ t, Real.negMulLog (x i) := by
  have e : Real.negMulLog (∑ i ∈ t, x i) = ∑ i ∈ t, -x i * Real.log (∑ j ∈ t, x j) := by
    rw [Real.negMulLog, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
  rw [e]
  apply Finset.sum_le_sum
  intro i hi
  rcases (hx i hi).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [Real.negMulLog]
    have : Real.log (x i) ≤ Real.log (∑ j ∈ t, x j) :=
      Real.log_le_log h (Finset.single_le_sum hx hi)
    nlinarith

theorem h44_entfin {α : Type*} (p : FiniteDistribution α) :
    p.entropy = ∑ a ∈ p.support, Real.negMulLog (p.weight a) := by
  unfold FiniteDistribution.entropy
  exact tsum_eq_sum (fun a ha => by rw [p.vanish a ha, Real.negMulLog_zero])

theorem h44_dp {α : Type*} {β : Type*} (p : FiniteDistribution α) (f : α → β) :
    (p.map f).entropy ≤ p.entropy := by
  rw [h44_entfin, h44_entfin]
  have hs : (p.map f).support = p.support.image f := rfl
  calc ∑ b ∈ (p.map f).support, Real.negMulLog ((p.map f).weight b)
      = ∑ b ∈ (p.map f).support, Real.negMulLog (∑ a ∈ p.support.filter (fun a => f a = b), p.weight a) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [h44_mapw, Finset.sum_filter]
    _ ≤ ∑ b ∈ (p.map f).support, ∑ a ∈ p.support.filter (fun a => f a = b), Real.negMulLog (p.weight a) := by
        apply Finset.sum_le_sum
        intro b _
        exact h44_nml_sum _ _ (fun a _ => p.nonneg a)
    _ = _ := by
        apply Finset.sum_fiberwise_of_maps_to
        intro a ha
        rw [hs]
        exact Finset.mem_image_of_mem f ha

theorem solution {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    p.js q ≤ (p.map f).js (q.map f)+(p.mix q).entropy-((p.mix q).map f).entropy := by
  have hm : ((p.map f).mix (q.map f)).entropy = ((p.mix q).map f).entropy := by
    unfold FiniteDistribution.entropy
    congr 1
    ext b
    congr 1
    have hS : (p.mix q).support = p.support ∪ q.support := rfl
    show ((p.map f).weight b + (q.map f).weight b) / 2 = _
    rw [h44_mapwS p f b (p.support ∪ q.support) Finset.subset_union_left,
      h44_mapwS q f b (p.support ∪ q.support) Finset.subset_union_right,
      h44_mapwS (p.mix q) f b (p.support ∪ q.support) hS.le, ← Finset.sum_add_distrib,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    show _ = if f a = b then (p.weight a + q.weight a) / 2 else 0
    split_ifs <;> simp
  have h1 := h44_dp p f
  have h2 := h44_dp q f
  unfold FiniteDistribution.js
  rw [hm]
  linarith

