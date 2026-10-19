-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.gridInformation_le_fine_add_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:28:00.581719+00:00
-- url     : https://prove2.me/submissions/86c34837-329f-469c-8184-106503f1c851

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/TranslationGain.lean:L266-L323
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.gridInformation_le_fine_add_boundary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Theorems.Thm_OAI_EntropyRateDimension_FiniteDistribution_js_le_map_add
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_map_affine
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_entropy_binary_extra
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_comp
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_relativeLabel_mem

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem negMulLog_sum_le {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  have hterm : ∀ i ∈ s,
      -(p i) * Real.log (∑ j ∈ s, p j) ≤ Real.negMulLog (p i) := by
    intro i hi
    rcases eq_or_lt_of_le (hp i hi) with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonpos_left
        (Real.log_le_log h (Finset.single_le_sum hp hi)) (neg_nonpos.mpr (hp i hi))
  have heq : (∑ i ∈ s, -(p i) * Real.log (∑ j ∈ s, p j)) =
      Real.negMulLog (∑ i ∈ s, p i) := by
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    rfl
  rw [← heq]
  exact Finset.sum_le_sum hterm

theorem observableEntropy_le {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ entropy s p := by
  classical
  calc
    observableEntropy s p f ≤
        ∑ b ∈ s.image f, ∑ a ∈ s.filter (fun a => f a = b), Real.negMulLog (p a) := by
      apply Finset.sum_le_sum
      intro b _
      exact negMulLog_sum_le _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = entropy s p :=
      Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

theorem observableEntropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (g ∘ f) ≤ observableEntropy s p f := by
  rw [observableEntropy_comp]
  exact observableEntropy_le _ _ _ (fun b _ => mass_nonneg s p f hp b)

theorem mass_subset {α : Type uα} {β : Type uβ} [DecidableEq β] {s t : Finset α}
    (p : α → ℝ) (f : α → β) (hst : s ⊆ t)
    (hp : ∀ x ∈ t, x ∉ s → p x = 0) (b : β) : mass s p f b = mass t p f b := by
  classical
  apply Finset.sum_subset (Finset.filter_subset_filter _ hst)
  intro x hx hn
  exact hp x (Finset.mem_filter.mp hx).1 (fun hs => hn (Finset.mem_filter.mpr ⟨hs,(Finset.mem_filter.mp hx).2⟩))

theorem observableEntropy_id {α : Type uα} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) : observableEntropy s p id = entropy s p := by
  simp only [observableEntropy, Finset.image_id, entropy, mass, id_eq]
  apply Finset.sum_congr rfl
  intro a ha
  simp [Finset.filter_eq',ha]

theorem conditionalEntropy_id {α : Type uα} {β : Type uβ} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (p : α → ℝ) (g : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p id g = entropy s p-observableEntropy s p g := by
  have hh := observableEntropy_comp_le s p (fun a => (a,g a)) Prod.fst hp
  change observableEntropy s p id ≤ _ at hh
  rw [observableEntropy_id] at hh
  have he := le_antisymm (observableEntropy_le s p (fun a => (a,g a)) hp) hh
  exact congrArg (fun x => x-observableEntropy s p g) he

theorem conditionalEntropy_midpoint {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (f : α → β) (g : α → γ) :
    (conditionalEntropy s p f g+conditionalEntropy s q f g)/2 ≤
      conditionalEntropy s (fun a => (p a+q a)/2) f g := by
  let P : Bool → α → ℝ := fun b => if b then p else q
  have hh := conditionalEntropy_mixture Finset.univ s (fun _ : Bool => (1/2 : ℝ))
    P f g (by intros; positivity) (by intro b _; cases b <;> assumption)
      (by intro b _; cases b <;> assumption)
  have he : (fun a => ∑ b : Bool, (1/2 : ℝ)*P b a) = fun a => (p a+q a)/2 := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [he] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte] at hh
  linarith

theorem js_observable_le {α : Type uα} {β : Type uβ} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (g : α → β) :
    observableEntropy s (fun a => (p a+q a)/2) g-
      (observableEntropy s p g+observableEntropy s q g)/2 ≤ js s p q := by
  have hh := conditionalEntropy_midpoint s p q hp hq hp1 hq1 id g
  rw [conditionalEntropy_id s p g hp, conditionalEntropy_id s q g hq,
    conditionalEntropy_id s _ g (fun a ha => div_nonneg (add_nonneg (hp a ha) (hq a ha)) (by norm_num))] at hh
  unfold js
  linarith

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

theorem entropy_on {α : Type uα} (p : FiniteDistribution α) (s : Finset α)
    (hs : p.support ⊆ s) : p.entropy=FiniteEntropy.entropy s p.weight := by
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hs h)), Real.negMulLog_zero]

theorem js_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.js q=FiniteEntropy.js s p.weight q.weight := by
  classical
  rw [js, (p.mix q).entropy_on s (Finset.union_subset hp hq), p.entropy_on s hp, q.entropy_on s hq]
  rfl

theorem map_weight_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) (b : β) :
    (p.map f).weight b=FiniteEntropy.mass s p.weight f b := by
  classical
  exact FiniteEntropy.mass_subset p.weight f hs (fun a _ ha => p.vanish a ha) b

theorem entropy_map_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) :
    (p.map f).entropy=FiniteEntropy.observableEntropy s p.weight f := by
  classical
  rw [(p.map f).entropy_on (s.image f) (Finset.image_subset_image hs)]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (p.map_weight_on f s hs b))

theorem mix_map_entropy {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hp : p.support ⊆ s) (hq : q.support ⊆ s) :
    ((p.map f).mix (q.map f)).entropy=
      FiniteEntropy.observableEntropy s (fun a => (p.weight a+q.weight a)/2) f := by
  classical
  rw [((p.map f).mix (q.map f)).entropy_on (s.image f)
    (Finset.union_subset (Finset.image_subset_image hp) (Finset.image_subset_image hq))]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change ((p.map f).weight b+(q.map f).weight b)/2=_
  rw [p.map_weight_on f s hp, q.map_weight_on f s hq]
  simp only [FiniteEntropy.mass, ← Finset.sum_div, Finset.sum_add_distrib]

theorem js_map_le {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    (p.map f).js (q.map f) ≤ p.js q := by
  classical
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [js, mix_map_entropy p q f s hp hq, p.entropy_map_on f s hp,
    q.entropy_map_on f s hq, p.js_on q s hp hq]
  exact FiniteEntropy.js_observable_le s _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on s hp) (q.sum_on s hq) f

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

theorem relativeLabel_measurable (s t u v : ℝ) : Measurable (relativeLabel s t u v) := by
  unfold relativeLabel
  exact (label_measurable s u).sub
    (((((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp (label_measurable t v)).const_mul (t/s)).add_const u).sub_const ((t/s)*v)).floor

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

theorem observationLaw_map_weight {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (g : β → γ) (c : γ) :
    ((observationLaw μ f hf s hs).map g).weight c = mass μ (g ∘ f) c := by
  classical
  rw [FiniteDistribution.map_weight_on _ _ s (fun _ h => h)]
  exact (mass_comp μ f hf s hs g c).symm

end MeasureEntropy

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Boundary ----
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace Boundary
open Set

theorem increment_eq_ite {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ) :
    increment a u = if ⌊u+a⌋=⌊u⌋ then 0 else 1 := by
  classical
  have hl := Int.floor_le_floor (show u ≤ u+a by linarith)
  have hu := Int.floor_le_floor (show u+a ≤ u+1 by linarith)
  rw [Int.floor_add_one] at hu
  by_cases h : ⌊u+a⌋=⌊u⌋
  · simp [increment,h]
  · have he : ⌊u+a⌋=⌊u⌋+1 := by omega
    simp [increment,he]

end Boundary

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TranslationGain ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

attribute [local instance] Classical.propDecidable

theorem mass_halfMix {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : α → β) (b : β) :
    mass ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) f b = (mass μ f b+mass ν f b)/2 := by
  unfold mass
  rw [Measure.real_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul,smul_eq_mul,ENNReal.toReal_add
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  rw [Measure.real_def,Measure.real_def]
  ring

theorem observationLaw_map_entropy {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (g : β → γ) :
    ((observationLaw μ f hf s hs).map g).entropy = entropy μ (g ∘ f) := by
  apply tsum_congr
  intro c
  rw [observationLaw_map_weight]

theorem mix_observationLaw_map_entropy {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂ν, f x ∈ t) (g : β → γ) :
    (((observationLaw μ f hf s hs).map g).mix
      ((observationLaw ν f hf t ht).map g)).entropy =
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) (g ∘ f) := by
  apply tsum_congr
  intro c
  congr 1
  change (((observationLaw μ f hf s hs).map g).weight c+
    ((observationLaw ν f hf t ht).map g).weight c)/2 = _
  rw [observationLaw_map_weight,observationLaw_map_weight,mass_halfMix]

theorem js_observationLaw_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂ν, f x ∈ t) (g : β → γ) :
    ((observationLaw μ f hf s hs).map g).js ((observationLaw ν f hf t ht).map g) =
      information μ ν (g ∘ f) := by
  rw [FiniteDistribution.js,mix_observationLaw_map_entropy,
    observationLaw_map_entropy,observationLaw_map_entropy]
  rfl

theorem information_le_map_add {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α → β) (hF : Measurable F) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, F x ∈ s) (ht : ∀ᵐ x ∂ν, F x ∈ t)
    (f : β → γ) (g : β → δ) :
    information μ ν (g ∘ F) ≤ information μ ν (f ∘ F)+
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) F-
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) (f ∘ F) := by
  classical
  let p := observationLaw μ F hF s hs
  let q := observationLaw ν F hF t ht
  have h := (p.js_map_le q g).trans (p.js_le_map_add q f)
  rw [js_observationLaw_map,js_observationLaw_map] at h
  have he : (p.mix q).entropy=entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) F := by
    apply tsum_congr
    intro b
    congr 1
    exact (mass_halfMix μ ν F b).symm
  have hf : ((p.mix q).map f).entropy = entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) (f ∘ F) := by
    rw [(p.mix q).entropy_map_on f (p.support ∪ q.support) (fun _ h => h)]
    change FiniteEntropy.observableEntropy (p.support ∪ q.support)
      (fun a => (p.weight a+q.weight a)/2) f = _
    rw [← FiniteDistribution.mix_map_entropy p q f (p.support ∪ q.support)
      Finset.subset_union_left Finset.subset_union_right]
    exact mix_observationLaw_map_entropy μ ν F hF s t hs ht f
  rwa [he,hf] at h

theorem fairShift_eq_halfMix (μ : Measure ℝ) (v : ℝ) :
    fairShift μ v = (1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • μ.map (fun x => x+v) := by
  norm_num [fairShift,Fin.sum_univ_two, ENNReal.ofReal_div_of_pos]

theorem relativeLabel_zero_of_good {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (u w x : ℝ)
    (hgood : ⌊u+(s/t)*(label s w x : ℝ)-(s/t)*w+s/t⌋ =
      ⌊u+(s/t)*(label s w x : ℝ)-(s/t)*w⌋) :
    relativeLabel t s u w x=0 := by
  let b := u+(s/t)*(label s w x : ℝ)-(s/t)*w
  let z := x/s+w-(label s w x : ℝ)
  have hz : 0 ≤ z := sub_nonneg.mpr (Int.floor_le _)
  have hz1 : z ≤ 1 := by
    change x/s+w-(⌊x/s+w⌋ : ℝ) ≤ 1
    linarith [Int.lt_floor_add_one (x/s+w)]
  have hl := Int.floor_le_floor (show b ≤ b+(s/t)*z from le_add_of_nonneg_right (mul_nonneg (div_pos hs ht).le hz))
  have hu := Int.floor_le_floor (show b+(s/t)*z ≤ b+s/t by nlinarith [div_pos hs ht])
  change ⌊b+s/t⌋=⌊b⌋ at hgood
  have hf : ⌊b+(s/t)*z⌋=⌊b⌋ := le_antisymm (hu.trans_eq hgood) hl
  have he : b+(s/t)*z=x/t+u := by
    dsimp [b,z]
    field_simp
    ring
  rw [he] at hf
  have hb : (s/t)*(label s w x : ℝ)+u-(s/t)*w=b := by dsimp [b]; ring
  unfold relativeLabel
  rw [hb]
  change ⌊x/t+u⌋-⌊b⌋=0
  omega

theorem gridInformation_le_fine_add_boundary (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s ≤ t) (u w : ℝ) :
    gridInformation μ v t u ≤ gridInformation μ v s w+
      (∫ x, Boundary.increment (s/t) (u+((s/t)*(label s w x : ℝ)-(s/t)*w)) ∂fairShift μ v)*Real.log 2 := by
  classical
  let ν := μ.map (fun x => x+v)
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const v).aemeasurable).2 inferInstance
  let := fairShift_probability μ v
  have hcν : CompactlyCarried ν := by simpa only [one_mul] using hμ.map_affine 1 v
  have hcρ := hμ.fairShift v
  let f := label s w
  let g := relativeLabel t s u w
  let F := fun x => (g x,f x)
  have hF : Measurable F := (relativeLabel_measurable t s u w).prodMk (label_measurable s w)
  have hceil : ⌈s/t⌉=(1 : ℤ) := by
    have hl := Int.ceil_pos.mpr (div_pos hs ht)
    have hu : ⌈s/t⌉ ≤ (1 : ℤ) := Int.ceil_le.mpr (by norm_num; exact (div_le_one ht).mpr hst)
    omega
  have hg : ∀ x, g x ∈ Finset.Icc (0 : ℤ) 1 := by
    intro x
    simpa only [hceil] using relativeLabel_mem ht hs u w x
  let aμ := Finset.Icc ⌊-hμ.choose/s+w⌋ ⌊hμ.choose/s+w⌋
  let aν := Finset.Icc ⌊-hcν.choose/s+w⌋ ⌊hcν.choose/s+w⌋
  have hfμ : ∀ᵐ x ∂μ, f x ∈ aμ := label_ae_finite μ hs hμ.choose_spec.2
  have hfν : ∀ᵐ x ∂ν, f x ∈ aν := label_ae_finite ν hs hcν.choose_spec.2
  have hFμ : ∀ᵐ x ∂μ, F x ∈ (Finset.Icc (0 : ℤ) 1) ×ˢ aμ := by
    filter_upwards [hfμ] with x hx
    exact Finset.mem_product.mpr ⟨hg x,hx⟩
  have hFν : ∀ᵐ x ∂ν, F x ∈ (Finset.Icc (0 : ℤ) 1) ×ˢ aν := by
    filter_upwards [hfν] with x hx
    exact Finset.mem_product.mpr ⟨hg x,hx⟩
  let r : ℤ × ℤ → ℤ := fun p => p.1+⌊(s/t)*(p.2 : ℝ)+u-(s/t)*w⌋
  have hr : r ∘ F=label t u := by
    funext x
    dsimp [r,F,g,f,relativeLabel]
    omega
  have hh := information_le_map_add μ ν F hF _ _ hFμ hFν Prod.snd r
  rw [hr,← fairShift_eq_halfMix] at hh
  change gridInformation μ v t u ≤ gridInformation μ v s w+entropy (fairShift μ v) F-
    entropy (fairShift μ v) f at hh
  let bad : ℤ → Prop := fun k => ⌊u+(s/t)*(k : ℝ)-(s/t)*w+s/t⌋ ≠ ⌊u+(s/t)*(k : ℝ)-(s/t)*w⌋
  have hgood : ∀ᵐ x ∂fairShift μ v, ¬bad (f x) → g x=0 := by
    apply Filter.Eventually.of_forall
    intro x hx
    apply relativeLabel_zero_of_good ht hs u w x
    exact not_not.mp hx
  have hb := entropy_binary_extra (fairShift μ v) f g (label_measurable s w)
    (relativeLabel_measurable t s u w) _ (label_ae_finite (fairShift μ v) hs hcρ.choose_spec.2)
    (Filter.Eventually.of_forall hg) bad hgood
  have he : (fun x => if bad (f x) then (1 : ℝ) else 0)=
      fun x => Boundary.increment (s/t) (u+((s/t)*(label s w x : ℝ)-(s/t)*w)) := by
    funext x
    rw [Boundary.increment_eq_ite (div_pos hs ht).le ((div_le_one ht).mpr hst)]
    simp only [bad,f,add_sub_assoc,ite_not]
  rw [he] at hb
  change entropy (fairShift μ v) F-entropy (fairShift μ v) f ≤ _ at hb
  linarith

end MeasureEntropy

end EntropyRateDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.gridInformation_le_fine_add_boundary := @_root_.OAI.EntropyRateDimension.MeasureEntropy.gridInformation_le_fine_add_boundary
