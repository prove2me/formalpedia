-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.mass_comp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:53:54.319398+00:00
-- url     : https://prove2.me/submissions/29ecddb8-4ef0-4a09-a3dd-900244824ddc

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L158-L183
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.mass_comp. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem mass_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) (c : γ) :
    mass μ (g ∘ f) c = FiniteEntropy.mass s (mass μ f) g c := by
  classical
  let t := s.filter (fun b => g b = c)
  have hd : (↑t : Set β).PairwiseDisjoint (fun b => {x | f x = b}) := by
    intro b _ d _ hbd
    exact Set.disjoint_left.mpr (fun _ hx hy => hbd (hx.symm.trans hy))
  have he : {x | g (f x) = c} =ᵐ[μ] ⋃ b ∈ t, {x | f x = b} := by
    filter_upwards [hs] with x hx
    apply propext
    change (g (f x) = c) ↔ x ∈ ⋃ b ∈ t, {x | f x = b}
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨f x,Finset.mem_filter.mpr ⟨hx,h⟩,rfl⟩
    · rintro ⟨b,hb,he⟩
      exact he ▸ (Finset.mem_filter.mp hb).2
  unfold mass
  change μ.real {x | g (f x) = c} = _
  rw [measureReal_congr he, measureReal_biUnion_finset hd]
  · rfl
  · intro b _
    exact (measurableSet_singleton b).preimage hf

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα,uβ,uγ} : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.mass_comp.{uα,uβ,uγ} := @_root_.OAI.EntropyRateDimension.MeasureEntropy.mass_comp.{uα,uβ,uγ}
