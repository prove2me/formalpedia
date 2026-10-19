-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteDistribution.tv_maps_le_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:19:42.162011+00:00
-- url     : https://prove2.me/submissions/5ec532b0-3fca-432e-be65-252b2691eaa4

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean:L35-L81
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteDistribution.tv_maps_le_disagreement. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem mass_subset {α : Type uα} {β : Type uβ} [DecidableEq β] {s t : Finset α}
    (p : α → ℝ) (f : α → β) (hst : s ⊆ t)
    (hp : ∀ x ∈ t, x ∉ s → p x = 0) (b : β) : mass s p f b = mass t p f b := by
  classical
  apply Finset.sum_subset (Finset.filter_subset_filter _ hst)
  intro x hx hn
  exact hp x (Finset.mem_filter.mp hx).1 (fun hs => hn (Finset.mem_filter.mpr ⟨hs,(Finset.mem_filter.mp hx).2⟩))

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteDistribution ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension

namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

theorem tv_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.tv q=FiniteEntropy.totalVariation s p.weight q.weight := by
  unfold tv FiniteEntropy.totalVariation
  congr 1
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hp h)), q.vanish a (fun h => ha (hq h)), sub_self, abs_zero]

theorem map_weight_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) (b : β) :
    (p.map f).weight b=FiniteEntropy.mass s p.weight f b := by
  classical
  exact FiniteEntropy.mass_subset p.weight f hs (fun a _ ha => p.vanish a ha) b

end FiniteDistribution

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.RandomGrid ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

theorem tv_maps_le_disagreement {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f g : α → β) :
    (p.map f).tv (p.map g) ≤ ∑ a ∈ p.support, if f a = g a then 0 else p.weight a := by
  classical
  let t := (p.map f).support ∪ (p.map g).support
  rw [(p.map f).tv_on (p.map g) t Finset.subset_union_left Finset.subset_union_right]
  unfold FiniteEntropy.totalVariation
  have hm (k : α → β) (b : β) : (p.map k).weight b =
      ∑ a ∈ p.support, if k a=b then p.weight a else 0 := by
    rw [map_weight_on p k p.support (fun _ h => h)]
    simp only [FiniteEntropy.mass,Finset.sum_filter]
  have hsum : ∑ b ∈ t, |(p.map f).weight b-(p.map g).weight b| ≤
      ∑ a ∈ p.support, if f a = g a then 0 else 2*p.weight a := by
    calc
      _ ≤ ∑ b ∈ t, ∑ a ∈ p.support,
          |(if f a=b then p.weight a else 0)-(if g a=b then p.weight a else 0)| := by
        apply Finset.sum_le_sum
        intro b _
        rw [hm f b,hm g b,← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : f a=g a
        · simp [h]
        · have hf : f a ∈ t := Finset.mem_union_left _ (Finset.mem_image_of_mem f ha)
          have hg : g a ∈ t := Finset.mem_union_right _ (Finset.mem_image_of_mem g ha)
          have habs : ∀ b, |(if f a=b then p.weight a else 0)-(if g a=b then p.weight a else 0)| =
              (if f a=b then p.weight a else 0)+(if g a=b then p.weight a else 0) := by
            intro b
            by_cases hfb : f a=b <;> by_cases hgb : g a=b
            · exact (h (hfb.trans hgb.symm)).elim
            · simp [hfb,hgb,abs_of_nonneg (p.nonneg a)]
            · simp [hfb,hgb,abs_of_nonneg (p.nonneg a)]
            · simp [hfb,hgb]
          simp_rw [habs]
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq,hf,hg,ite_true,h,ite_false]
          ring
  have he : (∑ a ∈ p.support, if f a=g a then 0 else 2*p.weight a) =
      2*∑ a ∈ p.support, if f a=g a then 0 else p.weight a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rw [he] at hsum
  linarith

end FiniteDistribution
namespace RandomGrid

attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability
end RandomGrid

namespace MeasureEntropy

end MeasureEntropy

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteDistribution
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteDistribution.tv_maps_le_disagreement.{uα,uβ} := @_root_.OAI.EntropyRateDimension.FiniteDistribution.tv_maps_le_disagreement.{uα,uβ}
