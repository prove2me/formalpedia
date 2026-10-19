-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.gridDeficit_eq_js
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:12:44.877625+00:00
-- url     : https://prove2.me/submissions/f2d26c8f-5e1c-45e3-ba9b-d8fb8c7183d9

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L994-L1009
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.gridDeficit_eq_js. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteDistribution_entropy_map_injective
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_map_affine
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_fairShift

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteDistribution ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension

namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

theorem entropy_congr {α : Type uα} (p q : FiniteDistribution α) (h : p.weight=q.weight) :
    p.entropy=q.entropy := by
  unfold entropy
  rw [h]

theorem map_weight_of_injective {α : Type uα} {β : Type uβ} (p : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) (a : α) :
    (p.map f).weight (f a)=p.weight a := by
  change FiniteEntropy.mass p.support p.weight f (f a)=p.weight a
  simp only [FiniteEntropy.mass, Finset.sum_filter, hf.eq_iff]
  rw [Finset.sum_ite_eq']
  by_cases ha : a ∈ p.support
  · simp only [ha, ↓reduceIte]
  · simp only [ha, ↓reduceIte, p.vanish a ha]

theorem translate_weight (p : FiniteDistribution ℤ) (j a : ℤ) :
    (p.translate j).weight a=p.weight (a-j) := by
  change (p.map (fun a => a+j)).weight a=p.weight (a-j)
  convert p.map_weight_of_injective (fun a => a+j) (add_left_injective j) (a-j) using 1; simp

end FiniteDistribution

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem fairShift_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    IsProbabilityMeasure (fairShift μ v) := by
  let ν := fun i : Fin 2 => μ.map (fun x => x+(i : ℝ)*v)
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const _).aemeasurable).2 inferInstance
  let := this
  exact mixture_probability ν (fun _ => 1/2) (by intro; positivity) (by norm_num [Fin.sum_univ_two])

theorem CompactlyCarried.fairShift {μ : Measure ℝ} (hμ : CompactlyCarried μ) (v : ℝ) :
    CompactlyCarried (fairShift μ v) := by
  apply CompactlyCarried.mixture
  intro i
  simpa only [one_mul] using hμ.map_affine 1 ((i : ℝ)*v)

theorem gridDeficit_eq_js (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    gridDeficit μ s u=(gridLaw μ hμ hs u).js ((gridLaw μ hμ hs u).translate 1) := by
  let := fairShift_probability μ s
  let p := gridLaw μ hμ hs u
  have he : (p.mix (p.translate 1)).weight=(gridLaw (fairShift μ s) (hμ.fairShift s) hs u).weight := by
    funext b
    change (p.weight b+(p.translate 1).weight b)/2=mass (fairShift μ s) (label s u) b
    rw [FiniteDistribution.translate_weight, mass_fairShift μ hs]
    rfl
  have ht : (p.translate 1).entropy=p.entropy :=
    FiniteDistribution.entropy_map_injective p (fun a : ℤ => a+1) (add_left_injective 1)
  rw [FiniteDistribution.js, FiniteDistribution.entropy_congr _ _ he, ht]
  change grid (fairShift μ s) s u-grid μ s u=
    grid (fairShift μ s) s u-(grid μ s u+grid μ s u)/2
  ring

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.gridDeficit_eq_js := @_root_.OAI.EntropyRateDimension.MeasureEntropy.gridDeficit_eq_js
