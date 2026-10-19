-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_translate_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:06:35.151693+00:00
-- url     : https://prove2.me/submissions/89fee425-cbc8-4f7e-8b80-9b3719d90f54

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L730-L753
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_translate_mixture. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_map_affine
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_nested_mixture
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

theorem averaged_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (b : ℝ) :
    averaged (μ.map (fun x => x+b)) s = averaged μ s := by
  simp only [averaged_eq_intervalIntegral, grid_translate]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ)] using
    (grid_periodic μ hμ hs).intervalIntegral_add_eq (b/s) 0

theorem averaged_nested_translate_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (b : ι → ℝ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    averaged μ s-averaged μ ((N : ℝ)*s) ≤
      averaged (∑ i, ENNReal.ofReal (w i) • μ.map (fun x => x+b i)) s-
      averaged (∑ i, ENNReal.ofReal (w i) • μ.map (fun x => x+b i)) ((N : ℝ)*s) := by
  let ν := fun i => μ.map (fun x => x+b i)
  have hp : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const (b i)).aemeasurable).2 inferInstance
  let := hp
  have hc : ∀ i, CompactlyCarried (ν i) := fun i => by
    simpa only [one_mul] using hμ.map_affine 1 (b i)
  let ρ := ∑ i, ENNReal.ofReal (w i) • ν i
  have hpρ := mixture_probability ν w hw hw1
  let := hpρ
  have hh := averaged_nested_mixture ρ (CompactlyCarried.mixture ν hc w) ν hc w hw rfl hs hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : ∀ i, averaged (ν i) s-averaged (ν i) ((N : ℝ)*s) =
      averaged μ s-averaged μ ((N : ℝ)*s) := by
    intro i
    rw [averaged_translate μ hμ hs, averaged_translate μ hμ (mul_pos hn hs)]
  simp_rw [he] at hh
  simpa only [← Finset.sum_mul, hw1, one_mul] using hh

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_translate_mixture.{uι} := @_root_.OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_translate_mixture.{uι}
