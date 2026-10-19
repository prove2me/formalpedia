-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.finiteConv_mean_gain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:22:30.166345+00:00
-- url     : https://prove2.me/submissions/0b8ef039-a5b7-4179-b882-883aecc99c58

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/PairGain.lean:L258-L306
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.finiteConv_mean_gain. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Theorems.Thm_OAI_EntropyRateDimension_FiniteDistribution_tv_maps_le_disagreement
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_js_le_tv
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_map_affine
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_fairShift
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_nested_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_scale
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_gridInformation_le_fine_add_boundary
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_integral_finite_observation
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_integral_gridInformation
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_comp

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

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

theorem observableEntropy_congr {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (p q : α → ℝ) (f g : α → β)
    (hp : ∀ x ∈ s, p x = q x) (hf : ∀ x ∈ s, f x = g x) :
    observableEntropy s p f = observableEntropy s q g := by
  classical
  have hi : s.image f = s.image g := Finset.image_congr hf
  have hm : ∀ b, mass s p f b = mass s q g b := by
    intro b
    simp only [mass, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hp x hx, hf x hx]
  simp only [observableEntropy, hi]
  rw [show mass s p f = mass s q g from funext hm]

theorem observableEntropy_le_of_fibers {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ] [Nonempty β]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, g x = g y → f x = f y) :
    observableEntropy s p f ≤ observableEntropy s p g := by
  classical
  let h : γ → β := fun c => if hc : ∃ x ∈ s, g x = c then f hc.choose else Classical.choice inferInstance
  have hf : ∀ x ∈ s, (h ∘ g) x = f x := by
    intro x hx
    dsimp only [Function.comp_apply,h]
    rw [dite_eq_left ⟨x,hx,rfl⟩]
    exact hfg _ (Exists.choose_spec (show ∃ y ∈ s, g y = g x from ⟨x,hx,rfl⟩)).1
      x hx (Exists.choose_spec (show ∃ y ∈ s, g y = g x from ⟨x,hx,rfl⟩)).2
  rw [← observableEntropy_congr s p p (h ∘ g) f (fun _ _ => rfl) hf]
  exact observableEntropy_comp_le s p g h hp

theorem observableEntropy_id {α : Type uα} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) : observableEntropy s p id = entropy s p := by
  simp only [observableEntropy, Finset.image_id, entropy, mass, id_eq]
  apply Finset.sum_congr rfl
  intro a ha
  simp [Finset.filter_eq',ha]

theorem observableEntropy_eq_of_fibers {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ] [Nonempty β] [Nonempty γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    observableEntropy s p f = observableEntropy s p g :=
  le_antisymm (observableEntropy_le_of_fibers s p f g hp
    (fun x hx y hy => (hfg x hx y hy).mpr))
    (observableEntropy_le_of_fibers s p g f hp
    (fun x hx y hy => (hfg x hx y hy).mp))

theorem observableEntropy_of_injective {α : Type uα} {β : Type uβ} [DecidableEq β] [Nonempty β]
    [Nonempty α] (s : Finset α) (p : α → ℝ) (f : α → β)
    (hp : ∀ x ∈ s, 0 ≤ p x) (hf : Function.Injective f) :
    observableEntropy s p f = entropy s p := by
  classical
  rw [← observableEntropy_id s p]
  exact observableEntropy_eq_of_fibers s p f id hp (fun _ _ _ _ => hf.eq_iff)

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

theorem tv_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.tv q=FiniteEntropy.totalVariation s p.weight q.weight := by
  unfold tv FiniteEntropy.totalVariation
  congr 1
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hp h)), q.vanish a (fun h => ha (hq h)), sub_self, abs_zero]

theorem js_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.js q=FiniteEntropy.js s p.weight q.weight := by
  classical
  rw [js, (p.mix q).entropy_on s (Finset.union_subset hp hq), p.entropy_on s hp, q.entropy_on s hq]
  rfl

theorem js_le_tv {α : Type uα} (p q : FiniteDistribution α) : p.js q ≤ p.tv q*Real.log 2 := by
  classical
  rw [p.tv_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right,
    p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.js_le_tv _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)

theorem map_weight_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) (b : β) :
    (p.map f).weight b=FiniteEntropy.mass s p.weight f b := by
  classical
  exact FiniteEntropy.mass_subset p.weight f hs (fun a _ ha => p.vanish a ha) b

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

theorem mass_le_one {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → β) (b : β) : mass μ f b ≤ 1 := by
  exact (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)

theorem entropy_nonneg {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → β) : 0 ≤ entropy μ f :=
  tsum_nonneg (fun b => Real.negMulLog_nonneg (mass_nonneg μ f b) (mass_le_one μ f b))

theorem entropy_eq_sum {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f = ∑ b ∈ s, Real.negMulLog (mass μ f b) := by
  apply tsum_eq_sum
  intro b hb
  rw [mass_eq_zero_of_ae μ f s hs hb, Real.negMulLog_zero]

theorem label_joint_measurable (s : ℝ) : Measurable (fun ux : ℝ × ℝ => label s ux.1 ux.2) :=
  ((measurable_snd.div_const s).add measurable_fst).floor

theorem measurable_mass_label (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) (b : ℤ) :
    Measurable (fun u => mass μ (label s u) b) := by
  have h := measurable_measure_prodMk_left (ν := μ)
    ((measurableSet_singleton b).preimage (label_joint_measurable s))
  exact h.ennreal_toReal

theorem measurable_grid (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    Measurable (grid μ s) :=
  Measurable.tsum (fun b => Real.continuous_negMulLog.measurable.comp (measurable_mass_label μ s b))

theorem label_ae_uniform (μ : Measure ℝ) {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, label s u x ∈ Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋ := by
  filter_upwards [label_ae_finite μ hs hB] with x hx
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨(Int.floor_le_floor (by linarith [hu.1] : -B/s ≤ -B/s+u)).trans hlo,
    hhi.trans (Int.floor_le_floor (by linarith [hu.2] : B/s+u ≤ B/s+1))⟩

theorem grid_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (s u : ℝ) : 0 ≤ grid μ s u :=
  entropy_nonneg μ _

theorem grid_le_card (μ : Measure ℝ) [IsProbabilityMeasure μ] {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    grid μ s u ≤ (Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card := by
  rw [grid, entropy_eq_sum μ _ _ (label_ae_uniform μ hs hB hu)]
  calc
    _ ≤ ∑ b ∈ Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      exact (Real.negMulLog_le_one_sub_self (mass_nonneg μ _ b)).trans
        (sub_le_self _ (mass_nonneg μ _ b))
    _ = _ := by simp

theorem grid_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) : Integrable (grid μ s) (volume.restrict (Set.Icc 0 1)) := by
  obtain ⟨B,_,hB⟩ := hμ
  apply (integrable_const ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)).mono'
    (measurable_grid μ s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (grid_nonneg μ s u)]
  exact grid_le_card μ hs hB hu

theorem entropy_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) :
    entropy μ (g ∘ f) = FiniteEntropy.observableEntropy s (mass μ f) g := by
  classical
  rw [entropy_eq_sum μ (g ∘ f) (s.image g) (hs.mono (fun _ hx => Finset.mem_image_of_mem g hx))]
  exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (mass_comp μ f hf s hs g b))

theorem entropy_comp_injective {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ] [Nonempty β] [Nonempty γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) (hg : Function.Injective g) :
    entropy μ (g ∘ f) = entropy μ f := by
  rw [entropy_comp μ f hf s hs g, FiniteEntropy.observableEntropy_of_injective s _ g
    (fun b _ => mass_nonneg μ f b) hg, entropy_eq_sum μ f s hs]
  rfl

theorem mass_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → γ) (hg : Measurable g) (c : γ) :
    mass (μ.map f) g c = mass μ (g ∘ f) c := by
  unfold mass Measure.real
  change ((μ.map f) (g ⁻¹' {c})).toReal = _
  rw [Measure.map_apply hf ((measurableSet_singleton c).preimage hg)]
  rfl

theorem entropy_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → γ) (hg : Measurable g) :
    entropy (μ.map f) g = entropy μ (g ∘ f) := by
  exact tsum_congr (fun c => congrArg Real.negMulLog (mass_map μ f hf g hg c))

theorem grid_periodic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) : Function.Periodic (grid μ s) 1 := by
  intro u
  obtain ⟨B,_,hB⟩ := hμ
  have he : label s (u+1) = (fun b : ℤ => b+1) ∘ label s u := by
    funext x
    simp only [label, Function.comp_apply]
    rw [← add_assoc, Int.floor_add_one]
  rw [grid, he, entropy_comp_injective μ (label s u) (label_measurable s u)
    _ (label_ae_finite μ hs hB) _ (add_left_injective 1)]
  rfl

theorem grid_translate (μ : Measure ℝ) (s u b : ℝ) :
    grid (μ.map (fun x => x+b)) s u = grid μ s (u+b/s) := by
  rw [grid, entropy_map μ (fun x => x+b) (measurable_id.add_const b) _ (label_measurable s u)]
  congr 1
  funext x
  simp only [Function.comp_apply, label, add_div]
  congr 1
  ring

theorem averaged_eq_intervalIntegral (μ : Measure ℝ) (s : ℝ) :
    averaged μ s = ∫ u in (0 : ℝ)..1, grid μ s u := by
  rw [averaged, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem grid_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    IntervalIntegrable (grid μ s) volume a b := by
  apply (grid_periodic μ hμ hs).intervalIntegrable₀ one_ne_zero
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr (grid_integrable μ hμ hs)

theorem averaged_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (b : ℝ) :
    averaged (μ.map (fun x => x+b)) s = averaged μ s := by
  simp only [averaged_eq_intervalIntegral, grid_translate]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ)] using
    (grid_periodic μ hμ hs).intervalIntegral_add_eq (b/s) 0

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

theorem increment_periodic (a : ℝ) : Function.Periodic (increment a) 1 := by
  intro u
  simp only [increment,add_right_comm u 1 a, Int.floor_add_one, Int.cast_add, Int.cast_one]
  ring

theorem increment_bounds {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ) :
    0 ≤ increment a u ∧ increment a u ≤ 1 := by
  have hl := Int.floor_le_floor (show u ≤ u+a by linarith)
  have hu := Int.floor_le_floor (show u+a ≤ u+1 by linarith)
  rw [Int.floor_add_one] at hu
  have hl' : (⌊u⌋ : ℝ) ≤ (⌊u+a⌋ : ℝ) := by exact_mod_cast hl
  have hu' : (⌊u+a⌋ : ℝ) ≤ (⌊u⌋ : ℝ)+1 := by exact_mod_cast hu
  unfold increment
  constructor <;> linarith

theorem increment_measurable (a : ℝ) : Measurable (increment a) := by
  unfold increment
  exact (((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
    (measurable_id.add_const a).floor)).sub
    ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp measurable_id.floor)

theorem increment_eq_indicator {a u : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    increment a u = (Icc (1-a) 1).indicator (fun _ => (1 : ℝ)) u := by
  have hfl : ⌊u⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hu.1.le,hu.2⟩
  by_cases h : 1-a ≤ u
  · have hf : ⌊u+a⌋=(1 : ℤ) := Int.floor_eq_iff.mpr (by
      norm_num
      constructor <;> linarith [hu.2])
    simp [increment,hfl,hf,Set.indicator_of_mem (show u ∈ Icc (1-a) 1 from ⟨h,hu.2.le⟩)]
  · have hf : ⌊u+a⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr (by constructor <;> linarith [hu.1])
    simp [increment,hfl,hf,Set.indicator_of_notMem (show u ∉ Icc (1-a) 1 from fun hh => h hh.1)]

theorem integral_increment {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ u in (0 : ℝ)..1, increment a u) = a := by
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo]
  have he := setIntegral_congr_fun (μ := (volume : Measure ℝ)) measurableSet_Ioo (fun u hu => increment_eq_indicator ha ha1 hu)
  rw [he,integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hi : (Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Icc 0 1 : Set ℝ) := Ioo_ae_eq_Icc
  have hs : (Icc (1-a) 1 ∩ Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Icc (1-a) 1 : Set ℝ) := by
    filter_upwards [hi] with u hu
    change (u ∈ Ioo (0 : ℝ) 1) = (u ∈ Icc 0 1) at hu
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,hu.mpr ⟨by linarith [h.1],h.2⟩⟩

  rw [Measure.restrict_congr_set hs,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,smul_eq_mul,mul_one]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-(1-a))]
  ring

theorem integral_increment_shift {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (b : ℝ) :
    (∫ u in (0 : ℝ)..1, increment a (u+b)) = a := by
  rw [intervalIntegral.integral_comp_add_right]
  have h := (increment_periodic a).intervalIntegral_add_eq b 0
  simpa only [zero_add,add_comm 1 b,integral_increment ha ha1] using h

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

theorem increment_prod_integrable {α : Type uα} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : α → ℝ) (hb : Measurable b) :
    Integrable (fun ux : ℝ × α => increment a (ux.1+b ux.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod μ) := by
  let : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  apply (integrable_const (1 : ℝ)).mono'
    ((increment_measurable a).comp (measurable_fst.add (hb.comp measurable_snd))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ux => by
    change ‖increment a (ux.1+b ux.2)‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg (increment_bounds ha ha1 _).1]
    exact (increment_bounds ha ha1 _).2)

theorem increment_measure_intervalIntegrable {α : Type uα} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : α → ℝ) (hb : Measurable b) :
    IntervalIntegrable (fun u => ∫ x, increment a (u+b x) ∂μ) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  exact (increment_prod_integrable μ ha ha1 b hb).integral_prod_left

theorem integral_increment_measure {α : Type uα} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : α → ℝ) (hb : Measurable b) :
    (∫ u in (0 : ℝ)..1, ∫ x, increment a (u+b x) ∂μ) = a := by
  have hp := increment_prod_integrable μ ha ha1 b hb
  have hs : Integrable (Function.uncurry (fun u x => increment a (u+b x)))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod μ) := by
    rw [uIoc_of_le zero_le_one]
    convert hp using 1
    rfl
  rw [intervalIntegral_integral_swap hs]
  simp only [integral_increment_shift ha ha1,integral_const,probReal_univ,one_smul]

end Boundary

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TranslationGain ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

theorem information_map_le_disagreement {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (T : α → α) (hT : Measurable T)
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂μ, f (T x) ∈ t) :
    information μ (μ.map T) f ≤ (∫ x, if f x=f (T x) then (0 : ℝ) else 1 ∂μ)*Real.log 2 := by
  classical
  let : IsProbabilityMeasure (μ.map T) := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 inferInstance
  let F := fun x => (f x,f (T x))
  have hF : Measurable F := hf.prodMk (hf.comp hT)
  have hst : ∀ᵐ x ∂μ, F x ∈ s ×ˢ t := by
    filter_upwards [hs,ht] with x hx hy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  let p := observationLaw μ F hF (s ×ˢ t) hst
  have he1 : (p.map Prod.fst).entropy=entropy μ f :=
    observationLaw_map_entropy μ F hF _ hst Prod.fst
  have he2 : (p.map Prod.snd).entropy=entropy (μ.map T) f := by
    rw [observationLaw_map_entropy,entropy_map μ T hT f hf]
    rfl
  have hem : ((p.map Prod.fst).mix (p.map Prod.snd)).entropy=
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • μ.map T) f := by
    apply tsum_congr
    intro b
    congr 1
    change ((p.map Prod.fst).weight b+(p.map Prod.snd).weight b)/2=_
    rw [observationLaw_map_weight,observationLaw_map_weight,mass_halfMix,
      mass_map μ T hT f hf]
    rfl
  have hi : (p.map Prod.fst).js (p.map Prod.snd)=information μ (μ.map T) f := by
    rw [FiniteDistribution.js,he1,he2,hem]
    rfl
  have hh := (p.map Prod.fst).js_le_tv (p.map Prod.snd)
  have ht' := p.tv_maps_le_disagreement Prod.fst Prod.snd
  have he : (∫ x, if f x=f (T x) then (0 : ℝ) else 1 ∂μ) =
      ∑ b ∈ p.support, if b.1=b.2 then 0 else p.weight b := by
    have h := integral_finite_observation μ F hF (s ×ˢ t) hst
      (fun b : β × β => if b.1=b.2 then (0 : ℝ) else 1)
    simpa only [F,p,observationLaw,mul_ite,mul_zero,mul_one] using h
  rw [hi] at hh
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_right ht' (Real.log_nonneg (by norm_num)))

theorem fairShift_eq_halfMix (μ : Measure ℝ) (v : ℝ) :
    fairShift μ v = (1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • μ.map (fun x => x+v) := by
  norm_num [fairShift,Fin.sum_univ_two, ENNReal.ofReal_div_of_pos]

theorem gridInformation_eq (μ : Measure ℝ) (v s u : ℝ) :
    gridInformation μ v s u = grid (fairShift μ v) s u-
      (grid μ s u+grid (μ.map (fun x => x+v)) s u)/2 := by
  rw [fairShift_eq_halfMix]
  rfl

theorem gridInformation_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (gridInformation μ v s) volume 0 1 := by
  let := fairShift_probability μ v
  let : IsProbabilityMeasure (μ.map (fun x => x+v)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const v).aemeasurable).2 inferInstance
  have hc : CompactlyCarried (μ.map (fun x => x+v)) := by simpa only [one_mul] using hμ.map_affine 1 v
  have he : gridInformation μ v s = fun u => grid (fairShift μ v) s u-
      (grid μ s u+grid (μ.map (fun x => x+v)) s u)/2 := funext (gridInformation_eq μ v s)
  rw [he]
  exact (grid_intervalIntegrable _ (hμ.fairShift v) hs 0 1).sub
    (((grid_intervalIntegrable μ hμ hs 0 1).add (grid_intervalIntegrable _ hc hs 0 1)).div_const 2)

theorem gridInformation_le_boundary (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (hvt : v ≤ t) (u : ℝ) :
    gridInformation μ v t u ≤ (∫ x, Boundary.increment (v/t) (u+x/t) ∂μ)*Real.log 2 := by
  classical
  obtain ⟨B,_,hB⟩ := hμ
  have h1 := label_ae_finite (u := u) μ ht hB
  have he : (fun x => label t u (x+v))=label t (u+v/t) := by
    funext x
    dsimp [label]
    congr 1
    ring
  have h2 : ∀ᵐ x ∂μ, label t u (x+v) ∈ Finset.Icc ⌊-B/t+(u+v/t)⌋ ⌊B/t+(u+v/t)⌋ := by
    filter_upwards [label_ae_finite (u := u+v/t) μ ht hB] with x hx
    rwa [congrFun he x]
  have hh := information_map_le_disagreement μ (fun x => x+v) (measurable_id.add_const v)
    (label t u) (label_measurable t u) _ _ h1 h2
  have hi : (fun x => if label t u x=label t u (x+v) then (0 : ℝ) else 1) =
      fun x => Boundary.increment (v/t) (u+x/t) := by
    funext x
    rw [Boundary.increment_eq_ite (div_nonneg hv.le ht.le) ((div_le_one ht).mpr hvt)]
    have hleft : ⌊u+x/t⌋=label t u x := by dsimp [label]; rw [add_comm]
    have hright : ⌊u+x/t+v/t⌋=label t u (x+v) := by dsimp [label]; congr 1; ring
    rw [hleft,hright]
    simp only [eq_comm]
  calc
    gridInformation μ v t u ≤ _ := hh
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hz : label t u x = label t u (x+v)
      · simpa only [ite_eq_left hz] using congrFun hi x
      · simpa only [ite_eq_right hz] using congrFun hi x

theorem averaged_fairShift_gain_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (hvt : v ≤ t) :
    averaged (fairShift μ v) t-averaged μ t ≤ (v/t)*Real.log 2 := by
  have hi := (Boundary.increment_measure_intervalIntegrable μ (div_nonneg hv.le ht.le)
    ((div_le_one ht).mpr hvt) (fun x => x/t) (measurable_id.div_const t)).mul_const (Real.log 2)
  have hh := intervalIntegral.integral_mono zero_le_one
    (gridInformation_intervalIntegrable μ hμ v ht) hi (fun u => gridInformation_le_boundary μ hμ hv ht hvt u)
  rw [integral_gridInformation μ hμ v ht,intervalIntegral.integral_mul_const,
    Boundary.integral_increment_measure μ (div_nonneg hv.le ht.le) ((div_le_one ht).mpr hvt)
      (fun x => x/t) (measurable_id.div_const t)] at hh
  exact hh

theorem averaged_fairShift_gain_compare (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) :
    averaged (fairShift μ v) t-averaged μ t ≤
      averaged (fairShift μ v) s-averaged μ s+(s/t)*Real.log 2 := by
  let := fairShift_probability μ v
  have hh (w : ℝ) : averaged (fairShift μ v) t-averaged μ t ≤
      gridInformation μ v s w+(s/t)*Real.log 2 := by
    let b := fun x => (s/t)*(label s w x : ℝ)-(s/t)*w
    have hb : Measurable b :=
      ((((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
        (label_measurable s w)).const_mul (s/t)).sub_const ((s/t)*w))
    have hi := (intervalIntegrable_const (c := gridInformation μ v s w)).add
      ((Boundary.increment_measure_intervalIntegrable (fairShift μ v) (div_pos hs ht).le
        ((div_le_one ht).mpr hst) b hb).mul_const (Real.log 2))
    have h := intervalIntegral.integral_mono zero_le_one
      (gridInformation_intervalIntegrable μ hμ v ht) hi
      (fun u => gridInformation_le_fine_add_boundary μ hμ v hs ht hst u w)
    rw [integral_gridInformation μ hμ v ht,
      intervalIntegral.integral_add intervalIntegrable_const
        ((Boundary.increment_measure_intervalIntegrable (fairShift μ v) (div_pos hs ht).le
          ((div_le_one ht).mpr hst) b hb).mul_const (Real.log 2)),
      intervalIntegral.integral_const,intervalIntegral.integral_mul_const,
      Boundary.integral_increment_measure (fairShift μ v) (div_pos hs ht).le
        ((div_le_one ht).mpr hst) b hb] at h
    simpa only [sub_zero,one_smul] using h
  have h := intervalIntegral.integral_mono zero_le_one
    (intervalIntegrable_const (c := averaged (fairShift μ v) t-averaged μ t))
    ((gridInformation_intervalIntegrable μ hμ v hs).add intervalIntegrable_const) hh
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (gridInformation_intervalIntegrable μ hμ v hs) intervalIntegrable_const,
    integral_gridInformation μ hμ v hs,intervalIntegral.integral_const] at h
  simpa only [sub_zero,one_smul] using h

theorem two_point_gain (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s v t : ℝ} (hs : 0 < s) (hsv : s < v) (hvt : v < t) :
    deficit μ v-(s/v+v/t)*Real.log 2 ≤
      (averaged (fairShift μ v) s-averaged (fairShift μ v) t)-(averaged μ s-averaged μ t) := by
  have hv := hs.trans hsv
  have ht := hv.trans hvt
  have hf := averaged_fairShift_gain_compare μ hμ v hs hv hsv.le
  have hc := averaged_fairShift_gain_le μ hμ hv ht hvt.le
  have hd : averaged (fairShift μ v) v-averaged μ v=deficit μ v := by
    rw [averaged_fairShift μ hμ hv]
    unfold deficit
    ring
  rw [hd] at hf
  nlinarith

end MeasureEntropy

end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FairPairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

theorem edge_mem_left {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.1 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).1

theorem edge_mem_right {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.2 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).2

theorem incident_sum {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ∑ x ∈ ν.support, incident w x = ∑ e, w e := by
  classical
  simp only [incident]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, edge_mem_left e, edge_mem_right e, ite_true]
  ring

theorem feasible_zero (ν : Law) (ℓ : ℤ) : Feasible (ν := ν) (ℓ := ℓ) (fun _ => 0) := by
  constructor
  · simp
  · intro x hx
    simpa [incident] using (ν.prob_pos x hx).le

theorem total_le_one {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ 1 := by
  rw [← incident_sum w, ← ν.prob_sum]
  exact Finset.sum_le_sum hw.2

theorem weight_le_one {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w)
    (e : ν.edges ℓ) : w e ≤ 1 := by
  exact (Finset.single_le_sum (fun a _ => hw.1 a) (Finset.mem_univ e)).trans (total_le_one hw)

theorem totals_nonempty (ν : Law) (ℓ : ℤ) :
    {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t}.Nonempty :=
  ⟨0, (fun _ => 0), feasible_zero ν ℓ, by simp⟩

theorem totals_bddAbove (ν : Law) (ℓ : ℤ) :
    BddAbove {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t} := by
  refine ⟨1, ?_⟩
  rintro t ⟨w, hw, rfl⟩
  exact total_le_one hw

theorem total_le_capacity {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ capacity ν ℓ :=
  le_csSup (totals_bddAbove ν ℓ) ⟨w, hw, rfl⟩

theorem feasible_isClosed (ν : Law) (ℓ : ℤ) :
    IsClosed {w : ν.edges ℓ → ℝ | Feasible w} := by
  classical
  change IsClosed ({w : ν.edges ℓ → ℝ | ∀ e, 0 ≤ w e} ∩
    {w | ∀ x ∈ ν.support, incident w x ≤ ν.prob x})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun e => isClosed_le continuous_const (continuous_apply e))
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    apply isClosed_le _ continuous_const
    unfold incident
    apply continuous_finsetSum
    intro e _
    apply Continuous.add <;> split_ifs <;> fun_prop

theorem feasible_isCompact (ν : Law) (ℓ : ℤ) :
    IsCompact {w : ν.edges ℓ → ℝ | Feasible w} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : ν.edges ℓ → ℝ) 1)).of_isClosed_subset
    (feasible_isClosed ν ℓ)
  intro w hw
  exact ⟨hw.1, weight_le_one hw⟩

theorem capacity_attained (ν : Law) (ℓ : ℤ) :
    ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = capacity ν ℓ := by
  obtain ⟨w, hw, hmax⟩ := (feasible_isCompact ν ℓ).exists_isMaxOn
    ⟨(fun _ => 0), feasible_zero ν ℓ⟩
    (continuous_finsetSum _ (fun e _ => continuous_apply e)).continuousOn
  refine ⟨w, hw, le_antisymm (total_le_capacity hw) ?_⟩
  apply csSup_le (totals_nonempty ν ℓ)
  rintro t ⟨v, hv, rfl⟩
  exact hmax hv

end FairPairs

end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.PairGain ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

theorem CompactlyCarried.shiftLaw {μ : Measure ℝ} (hμ : CompactlyCarried μ) (b : ℝ) :
    CompactlyCarried (shiftLaw μ b) := by simpa only [one_mul,MeasureEntropy.shiftLaw] using hμ.map_affine 1 b

theorem window_shiftLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (b : ℝ) :
    window (shiftLaw μ b) s t = window μ s t := by
  simp only [window,shiftLaw,averaged_translate μ hμ hs,averaged_translate μ hμ ht]

theorem CompactlyCarried.pairLaw {μ : Measure ℝ} (hμ : CompactlyCarried μ) (x y : ℝ) :
    CompactlyCarried (pairLaw μ x y) := by
  have hh := CompactlyCarried.mixture (fun i : Fin 2 => MeasureEntropy.shiftLaw μ (if i=0 then x else y))
    (fun i => hμ.shiftLaw _) (fun _ => (1/2 : ℝ))
  simpa [Fin.sum_univ_two,MeasureEntropy.pairLaw] using hh

theorem pairLaw_comm (μ : Measure ℝ) (x y : ℝ) : pairLaw μ x y=pairLaw μ y x := add_comm _ _

theorem pairLaw_eq_shift_fair (μ : Measure ℝ) (x y : ℝ) :
    pairLaw μ x y = shiftLaw (fairShift μ (y-x)) x := by
  simp only [pairLaw,shiftLaw,fairShift,Fin.sum_univ_two,Fin.val_zero,Fin.val_one,
    Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero]
  rw [Measure.map_add _ _ (by fun_prop),
    Measure.map_smul (f := fun z : ℝ => z+x) _ _,
    Measure.map_smul (f := fun z : ℝ => z+x) _ _,
    Measure.map_map (g := fun z : ℝ => z+x) (f := fun z : ℝ => z) (by fun_prop) (by fun_prop),
    Measure.map_map (g := fun z : ℝ => z+x) (f := fun z : ℝ => z+(y-x)) (by fun_prop) (by fun_prop)]
  have he : (fun z : ℝ => z+x) ∘ (fun z => z+(y-x))=(fun z => z+y) := by
    funext z; simp; ring
  rw [he]
  rfl

theorem pairLaw_gain (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s t x y : ℝ} (hs : 0 < s) (hsv : s < |y-x|) (hvt : |y-x| < t) :
    deficit μ |y-x|-(s/|y-x|+|y-x|/t)*Real.log 2 ≤
      window (pairLaw μ x y) s t-window μ s t := by
  have hv : 0 < |y-x| := hs.trans hsv
  have ht : 0 < t := hv.trans hvt
  let (v : ℝ) : IsProbabilityMeasure (fairShift μ v) := fairShift_probability μ v
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at *
    rw [pairLaw_eq_shift_fair,window_shiftLaw _ (hμ.fairShift _) hs ht]
    exact two_point_gain μ hμ hs hsv hvt
  · have he : |y-x|=x-y := by rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hsv' : s < x-y := he ▸ hsv
    have hvt' : x-y < t := he ▸ hvt
    rw [he,pairLaw_comm,pairLaw_eq_shift_fair,window_shiftLaw _ (hμ.fairShift _) hs ht]
    exact two_point_gain μ hμ hs hsv' hvt'

theorem CompactlyCarried.finiteConv {μ : Measure ℝ} (hμ : CompactlyCarried μ)
    (ν : FairPairs.Law) (a : ℝ) : CompactlyCarried (finiteConv ν a μ) :=
  CompactlyCarried.mixture _ (fun _ => hμ.shiftLaw _) _

theorem deficit_mixture {α : Type uα} [Fintype α]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : α → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : ∀ i, CompactlyCarried (ν i))
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (hm : μ=∑ i, ENNReal.ofReal (p i) • ν i) {v : ℝ} (hv : 0 < v) :
    deficit μ v ≤ ∑ i, p i*deficit (ν i) v := by
  have hh := averaged_nested_mixture μ hμ ν hν p hp hm hv (by norm_num : 0 < (2 : ℕ))
  simp only [deficit,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hp1,one_mul]
  push_cast at hh
  simp only [mul_sub,Finset.sum_sub_distrib] at hh
  linarith

theorem deficit_scale (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {v a : ℝ} (hv : 0 < v) (ha : a ≠ 0) :
    deficit (μ.map (fun x => a*x)) v=deficit μ (v/|a|) := by
  rw [deficit,averaged_scale μ hμ hv ha,averaged_scale μ hμ (by positivity) ha,deficit]
  congr 2
  ring_nf

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.FairPairs
open MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal

theorem incident_smul_sum (ν : Law) (ℓ : ℤ) (w : ν.edges ℓ → ℝ) (hw : ∀ e, 0 ≤ w e)
    (f : ℝ → Measure ℝ) :
    (∑ x ∈ ν.support, ENNReal.ofReal (incident w x) • f x) =
      ∑ e, (ENNReal.ofReal (w e/2) • f e.val.1+ENNReal.ofReal (w e/2) • f e.val.2) := by
  classical
  have hw2 : ∀ e, 0 ≤ w e/2 := fun e => div_nonneg (hw e) (by norm_num)
  have hv : ∀ x e, 0 ≤ (if e.val.1=x then w e/2 else 0)+(if e.val.2=x then w e/2 else 0) := by
    intro x e
    have hwe := hw2 e
    split_ifs <;> positivity
  simp only [incident,ENNReal.ofReal_sum_of_nonneg (fun e _ => hv _ e),Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hh : ∀ x, ENNReal.ofReal ((if e.val.1=x then w e/2 else 0)+
      (if e.val.2=x then w e/2 else 0)) • f x =
      (if e.val.1=x then ENNReal.ofReal (w e/2) • f e.val.1 else 0)+
      (if e.val.2=x then ENNReal.ofReal (w e/2) • f e.val.2 else 0) := by
    intro x
    have hwe := hw2 e
    rw [ENNReal.ofReal_add (by split_ifs <;> positivity) (by split_ifs <;> positivity)]
    rw [add_smul]
    congr 1 <;> split_ifs <;> simp_all only [ENNReal.ofReal_zero,zero_smul]
  simp_rw [hh,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,edge_mem_left e,edge_mem_right e,ite_true]

theorem residual_nonneg {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w)
    (x : ν.support) : 0 ≤ residual w x := sub_nonneg.mpr (hw.2 x x.property)

theorem residual_total {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    (∑ x : ν.support, residual w x)+(∑ e, w e)=1 := by
  classical
  simp only [residual,Finset.sum_sub_distrib,ν.subtype_sum,
    Finset.sum_coe_sort ν.support (fun x => incident w x),incident_sum]
  ring

theorem decompositionWeight_nonneg {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∀ z, 0 ≤ decompositionWeight w z := by
  intro z
  cases z with
  | inl e => exact hw.1 e
  | inr x => exact residual_nonneg hw x

theorem decompositionWeight_sum {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ∑ z, decompositionWeight w z=1 := by
  rw [Fintype.sum_sum_type]
  exact (add_comm _ _).trans (residual_total w)

theorem decompositionLaw_compact {ν : Law} {ℓ : ℤ} (μ : Measure ℝ) (hμ : CompactlyCarried μ)
    (a : ℝ) (z : ν.edges ℓ ⊕ ν.support) : CompactlyCarried (decompositionLaw μ a z) := by
  cases z with
  | inl e => exact hμ.pairLaw _ _
  | inr x => exact hμ.shiftLaw _

theorem finiteConv_decomposition (ν : Law) (ℓ : ℤ) (w : ν.edges ℓ → ℝ) (hw : Feasible w)
    (μ : Measure ℝ) (a : ℝ) :
    finiteConv ν a μ = ∑ z, ENNReal.ofReal (decompositionWeight w z) • decompositionLaw μ a z := by
  classical
  rw [Fintype.sum_sum_type]
  change finiteConv ν a μ=(∑ e, ENNReal.ofReal (w e) • pairLaw μ (a*e.val.1) (a*e.val.2))+
    ∑ x : ν.support, ENNReal.ofReal (residual w x) • shiftLaw μ (a*x)
  have he : ∀ e : ν.edges ℓ, ENNReal.ofReal (w e) • pairLaw μ (a*e.val.1) (a*e.val.2)=
      ENNReal.ofReal (w e/2) • shiftLaw μ (a*e.val.1)+
      ENNReal.ofReal (w e/2) • shiftLaw μ (a*e.val.2) := by
    intro e
    simp only [pairLaw,smul_add,smul_smul,← ENNReal.ofReal_mul (hw.1 e)]
    congr 2 <;> congr 1 <;> ring
  simp_rw [he]
  rw [← incident_smul_sum ν ℓ w hw.1 (fun x => shiftLaw μ (a*x)),← Finset.sum_coe_sort ν.support (fun x =>
    ENNReal.ofReal (incident w x) • shiftLaw μ (a*x)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hi : 0 ≤ incident w x := by
    apply Finset.sum_nonneg
    intro e _
    have hre := hw.1 e
    split_ifs <;> positivity
  rw [← add_smul,← ENNReal.ofReal_add hi (residual_nonneg hw x)]
  simp only [residual,add_sub_cancel]

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory FairPairs
open scoped BigOperators ENNReal

theorem finiteConv_gain (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ) {ℓ : ℤ}
    (w : ν.edges ℓ → ℝ) (hw : FairPairs.Feasible w)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N)
    (hv : ∀ e : ν.edges ℓ, s < |a*e.val.2-a*e.val.1| ∧ |a*e.val.2-a*e.val.1| < N*s) :
    (∑ e, w e*(deficit μ |a*e.val.2-a*e.val.1|-
      (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) ≤
      window (finiteConv ν a μ) s (N*s)-window μ s (N*s) := by
  classical
  have ht : 0 < (N : ℝ)*s := mul_pos (by exact_mod_cast hN) hs
  have hh := averaged_nested_mixture (finiteConv ν a μ) (hμ.finiteConv ν a)
    (decompositionLaw (ν := ν) (ℓ := ℓ) μ a) (decompositionLaw_compact μ hμ a)
    (decompositionWeight w) (decompositionWeight_nonneg hw)
    (finiteConv_decomposition ν ℓ w hw μ a) hs hN
  change (∑ z, decompositionWeight w z*window (decompositionLaw μ a z) s (N*s)) ≤ _ at hh
  have hid : (∑ z, decompositionWeight w z*window (decompositionLaw μ a z) s (N*s))-
      window μ s (N*s) =
      ∑ e, w e*(window (pairLaw μ (a*e.val.1) (a*e.val.2)) s (N*s)-window μ s (N*s)) := by
    calc
      _ = (∑ z, decompositionWeight w z*window (decompositionLaw μ a z) s (N*s))-
          ∑ z, decompositionWeight w z*window μ s (N*s) := by
        rw [← Finset.sum_mul,decompositionWeight_sum,one_mul]
      _ = ∑ z, decompositionWeight w z*(window (decompositionLaw μ a z) s (N*s)-
          window μ s (N*s)) := by simp only [mul_sub,Finset.sum_sub_distrib]
      _ = _ := by
        rw [Fintype.sum_sum_type]
        simp only [decompositionWeight,decompositionLaw,Sum.elim_inl,Sum.elim_inr,
          window_shiftLaw μ hμ hs ht,sub_self,mul_zero,Finset.sum_const_zero,add_zero]
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun (e : ν.edges ℓ) _ =>
    mul_le_mul_of_nonneg_left (pairLaw_gain μ hμ hs (hv e).1 (hv e).2) (hw.1 e))
  rw [← hid] at hl
  exact hl.trans (sub_le_sub_right hh _)

theorem finiteConv_mean_gain {β : Type uβ} [Fintype β]
    (ν : FairPairs.Law) (a b : ℝ) (hb : b ≠ 0)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (τ : β → Measure ℝ) [∀ z, IsProbabilityMeasure (τ z)]
    (hτ : ∀ z, CompactlyCarried (τ z))
    (p : β → ℝ) (hp : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z=1)
    (hm : μ.map (fun x => b*x) = ∑ z, ENNReal.ofReal (p z) • τ z)
    {δ η s : ℝ} (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) (hs : 0 < s)
    {N : ℕ} (hN : 0 < N) (ℓ : ℤ)
    (hv : ∀ e : ν.edges ℓ, s < |a*e.val.2-a*e.val.1| ∧ |a*e.val.2-a*e.val.1| < N*s)
    (herr : ∀ e : ν.edges ℓ,
      (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2 ≤ η) :
    (δ-η)*FairPairs.capacity ν ℓ ≤
      ∑ z, p z*(window (finiteConv ν a (τ z)) s (N*s)-window (τ z) s (N*s)) := by
  classical
  obtain ⟨w,hw,he⟩ := FairPairs.capacity_attained ν ℓ
  let : IsProbabilityMeasure (μ.map (fun x => b*x)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_const.mul measurable_id).aemeasurable).2 inferInstance
  have hmcomp : CompactlyCarried (μ.map (fun x => b*x)) := by
    simpa only [add_zero] using hμ.map_affine b 0
  have hdef (e : ν.edges ℓ) : δ ≤ ∑ z, p z*deficit (τ z) |a*e.val.2-a*e.val.1| := by
    have hpv := hs.trans (hv e).1
    have hd := deficit_mixture (μ.map (fun x => b*x)) hmcomp τ hτ p hp hp1 hm hpv
    rw [deficit_scale μ hμ hpv hb] at hd
    exact (hδ _ (div_pos hpv (abs_pos.mpr hb))).trans hd
  have hz (z : β) := finiteConv_gain ν a (τ z) (hτ z) w hw hs hN hv
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hz z) (hp z))
  simp_rw [Finset.mul_sum] at hsum
  rw [Finset.sum_comm] at hsum
  have hlo : (δ-η)*FairPairs.capacity ν ℓ ≤
      ∑ e, ∑ z, p z*(w e*(deficit (τ z) |a*e.val.2-a*e.val.1|-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) := by
    rw [← he,mul_comm,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e _
    have hh : ∑ z, p z*(w e*(deficit (τ z) |a*e.val.2-a*e.val.1|-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) =
        w e*((∑ z, p z*deficit (τ z) |a*e.val.2-a*e.val.1|)-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2) := by
      simp_rw [show ∀ z, p z*(w e*(deficit (τ z) |a*e.val.2-a*e.val.1|-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) =
        w e*(p z*deficit (τ z) |a*e.val.2-a*e.val.1|)-
        w e*p z*((s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2) by intro z; ring]
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,← Finset.mul_sum,hp1]
      ring
    rw [hh]
    exact mul_le_mul_of_nonneg_left (sub_le_sub (hdef e) (herr e)) (hw.1 e)
  exact hlo.trans hsum

end EntropyRateDimension.MeasureEntropy

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open MeasureTheory FairPairs
open scoped BigOperators ENNReal


theorem solution.{uβ} : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.finiteConv_mean_gain.{uβ} := @_root_.OAI.EntropyRateDimension.MeasureEntropy.finiteConv_mean_gain.{uβ}
