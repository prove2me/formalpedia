-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.entropy_binary_extra
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:24:30.847351+00:00
-- url     : https://prove2.me/submissions/a6feac40-fada-46d0-acea-27e56533cb5f

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean:L163-L215
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.entropy_binary_extra. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_le_bad_mass
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_integral_finite_observation
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_comp

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem observableEntropy_id {α : Type uα} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) : observableEntropy s p id = entropy s p := by
  simp only [observableEntropy, Finset.image_id, entropy, mass, id_eq]
  apply Finset.sum_congr rfl
  intro a ha
  simp [Finset.filter_eq',ha]

end FiniteEntropy
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

theorem entropy_eq_sum {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f = ∑ b ∈ s, Real.negMulLog (mass μ f b) := by
  apply tsum_eq_sum
  intro b hb
  rw [mass_eq_zero_of_ae μ f s hs hb, Real.negMulLog_zero]

theorem entropy_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) :
    entropy μ (g ∘ f) = FiniteEntropy.observableEntropy s (mass μ f) g := by
  classical
  rw [entropy_eq_sum μ (g ∘ f) (s.image g) (hs.mono (fun _ hx => Finset.mem_image_of_mem g hx))]
  exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (mass_comp μ f hf s hs g b))

end MeasureEntropy
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

end FiniteDistribution
namespace RandomGrid

attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability
end RandomGrid

namespace MeasureEntropy

theorem entropy_binary_extra {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (g : α → ℤ)
    (hf : Measurable f) (hg : Measurable g) (s : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (hg01 : ∀ᵐ x ∂μ, g x ∈ Finset.Icc (0 : ℤ) 1)
    (bad : β → Prop) [DecidablePred bad]
    (hgood : ∀ᵐ x ∂μ, ¬bad (f x) → g x=0) :
    entropy μ (fun x => (g x,f x))-entropy μ f ≤
      (∫ x, if bad (f x) then (1 : ℝ) else 0 ∂μ)*Real.log 2 := by
  classical
  let t := ((Finset.Icc (0 : ℤ) 1) ×ˢ s).filter (fun y => bad y.2 ∨ y.1=0)
  let F := fun x => (g x,f x)
  have hF : Measurable F := hg.prodMk hf
  have ht : ∀ᵐ x ∂μ, F x ∈ t := by
    filter_upwards [hs,hg01,hgood] with x hx hgx hgoodx
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hgx,hx⟩,or_iff_not_imp_left.mpr hgoodx⟩
  have hh := FiniteEntropy.conditionalEntropy_le_bad_mass t (mass μ F) Prod.fst Prod.snd bad
    (fun a _ => mass_nonneg μ F a) (by
      intro a ha b hb hab hbad
      have ha' := (Finset.mem_filter.mp ha).2.resolve_left hbad
      have hb' := (Finset.mem_filter.mp hb).2.resolve_left (hab ▸ hbad)
      exact ha'.trans hb'.symm)
  have hi : (fun a : ℤ × β => (a.1,a.2))=id := rfl
  unfold FiniteEntropy.conditionalEntropy at hh
  rw [hi,FiniteEntropy.observableEntropy_id,← entropy_comp μ F hF t ht Prod.snd] at hh
  change FiniteEntropy.entropy t (mass μ F)-entropy μ f ≤ _ at hh
  unfold FiniteEntropy.entropy at hh
  rw [← entropy_eq_sum μ F t ht] at hh
  have hbad0 : 0 ≤ ∑ a ∈ t, if bad a.2 then mass μ F a else 0 := by
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact mass_nonneg μ F a
    · exact le_rfl
  have hc : (t.image Prod.fst).card ≤ 2 := by
    have hsub : t.image Prod.fst ⊆ Finset.Icc (0 : ℤ) 1 := by
      rintro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).1
    simpa using Finset.card_le_card hsub
  have hl : Real.log (t.image Prod.fst).card ≤ Real.log 2 := by
    by_cases hz : (t.image Prod.fst).card=0
    · simp [hz,Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    · apply Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz))
      exact_mod_cast hc
  have he : (∫ x, if bad (f x) then (1 : ℝ) else 0 ∂μ) =
      ∑ a ∈ t, if bad a.2 then mass μ F a else 0 := by
    have h := integral_finite_observation μ F hF t ht
      (fun a : ℤ × β => if bad a.2 then (1 : ℝ) else 0)
    simpa only [F, mul_ite, mul_one, mul_zero] using h

  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_left hl hbad0)

end MeasureEntropy

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.entropy_binary_extra.{uα,uβ} := @_root_.OAI.EntropyRateDimension.MeasureEntropy.entropy_binary_extra.{uα,uβ}
