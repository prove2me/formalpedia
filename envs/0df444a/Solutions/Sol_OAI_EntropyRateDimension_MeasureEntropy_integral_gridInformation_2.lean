-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.integral_gridInformation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:26:05.855873+00:00
-- url     : https://prove2.me/submissions/b24d92a6-f066-4b35-9774-768357d88edb

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/TranslationGain.lean:L179-L192
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.integral_gridInformation. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_map_affine
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_mixture
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

theorem fairShift_eq_halfMix (μ : Measure ℝ) (v : ℝ) :
    fairShift μ v = (1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • μ.map (fun x => x+v) := by
  norm_num [fairShift,Fin.sum_univ_two, ENNReal.ofReal_div_of_pos]

theorem gridInformation_eq (μ : Measure ℝ) (v s u : ℝ) :
    gridInformation μ v s u = grid (fairShift μ v) s u-
      (grid μ s u+grid (μ.map (fun x => x+v)) s u)/2 := by
  rw [fairShift_eq_halfMix]
  rfl

theorem integral_gridInformation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ u in (0 : ℝ)..1, gridInformation μ v s u) = averaged (fairShift μ v) s-averaged μ s := by
  let := fairShift_probability μ v
  let : IsProbabilityMeasure (μ.map (fun x => x+v)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const v).aemeasurable).2 inferInstance
  have hc : CompactlyCarried (μ.map (fun x => x+v)) := by simpa only [one_mul] using hμ.map_affine 1 v
  simp_rw [gridInformation_eq]
  rw [intervalIntegral.integral_sub (grid_intervalIntegrable _ (hμ.fairShift v) hs 0 1)
      (((grid_intervalIntegrable μ hμ hs 0 1).add (grid_intervalIntegrable _ hc hs 0 1)).div_const 2),
    intervalIntegral.integral_div,intervalIntegral.integral_add (grid_intervalIntegrable μ hμ hs 0 1)
      (grid_intervalIntegrable _ hc hs 0 1),← averaged_eq_intervalIntegral,← averaged_eq_intervalIntegral,
    ← averaged_eq_intervalIntegral,averaged_translate μ hμ hs v]
  ring

end MeasureEntropy

end EntropyRateDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.integral_gridInformation := @_root_.OAI.EntropyRateDimension.MeasureEntropy.integral_gridInformation
