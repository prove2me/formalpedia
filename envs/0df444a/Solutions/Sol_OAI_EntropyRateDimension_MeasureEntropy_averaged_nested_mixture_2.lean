-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:03:11.909263+00:00
-- url     : https://prove2.me/submissions/f4b6ae18-f77c-412b-b5f2-33392898222f

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L677-L703
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_mixture. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_mixture
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

theorem conditionalEntropy_id {α : Type uα} {β : Type uβ} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (p : α → ℝ) (g : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p id g = entropy s p-observableEntropy s p g := by
  have hh := observableEntropy_comp_le s p (fun a => (a,g a)) Prod.fst hp
  change observableEntropy s p id ≤ _ at hh
  rw [observableEntropy_id] at hh
  have he := le_antisymm (observableEntropy_le s p (fun a => (a,g a)) hp) hh
  exact congrArg (fun x => x-observableEntropy s p g) he

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

theorem averaged_eq_intervalIntegral (μ : Measure ℝ) (s : ℝ) :
    averaged μ s = ∫ u in (0 : ℝ)..1, grid μ s u := by
  rw [averaged, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem grid_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    IntervalIntegrable (grid μ s) volume a b := by
  apply (grid_periodic μ hμ hs).intervalIntegrable₀ one_ne_zero
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr (grid_integrable μ hμ hs)

theorem averaged_grid_nsmul (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    (∫ u in (0 : ℝ)..1, grid μ s ((N : ℝ)*u)) = averaged μ s := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [intervalIntegral.integral_comp_mul_left _ hNr, mul_zero, mul_one]
  have he := (grid_periodic μ hμ hs).intervalIntegral_add_zsmul_eq (N : ℤ) 0
    (grid_intervalIntegrable μ hμ hs)
  simp only [zsmul_eq_mul, zero_add, Int.cast_natCast, mul_one] at he
  rw [he, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hNr, one_mul, averaged_eq_intervalIntegral]

theorem label_nested (s u x : ℝ) {N : ℕ} (hN : 0 < N) :
    label ((N : ℝ)*s) u x = label s ((N : ℝ)*u) x / (N : ℤ) := by
  simp only [label]
  rw [← Int.floor_div_natCast]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [add_div, mul_div_cancel_left₀ u hn]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem mass_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (ν : ι → Measure α) [∀ i, IsFiniteMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i) (f : α → β) (b : β) :
    mass μ f b = ∑ i, w i*mass (ν i) f b := by
  unfold mass
  rw [hm]
  simp only [Measure.real_def, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i)]

theorem entropy_coarsening_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    [DecidableEq β] [DecidableEq γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : ι → Measure α)
    [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    (f : α → β) (hf : Measurable f) (s : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (hsi : ∀ i, ∀ᵐ x ∂ν i, f x ∈ s) (g : β → γ) :
    (∑ i, w i*(entropy (ν i) f-entropy (ν i) (g ∘ f))) ≤
      entropy μ f-entropy μ (g ∘ f) := by
  classical
  have hh := FiniteEntropy.conditionalEntropy_mixture Finset.univ s w
    (fun i => mass (ν i) f) id g (fun i _ => hw i)
    (fun i _ b _ => mass_nonneg (ν i) f b) (fun i _ => mass_sum (ν i) f hf s (hsi i))
  have he : (fun b => ∑ i, w i*mass (ν i) f b) = mass μ f :=
    funext (fun b => (mass_mixture μ ν w hw hm f b).symm)
  rw [he, FiniteEntropy.conditionalEntropy_id _ _ _ (fun b _ => mass_nonneg μ f b)] at hh
  have hi : ∀ i, FiniteEntropy.conditionalEntropy s (mass (ν i) f) id g =
      entropy (ν i) f-entropy (ν i) (g ∘ f) := by
    intro i
    rw [FiniteEntropy.conditionalEntropy_id _ _ _ (fun b _ => mass_nonneg (ν i) f b),
      ← entropy_comp (ν i) f hf s (hsi i) g, entropy_eq_sum (ν i) f s (hsi i)]
    rfl
  simp_rw [hi] at hh
  rw [← entropy_comp μ f hf s hs g] at hh
  rw [entropy_eq_sum μ f s hs]
  exact hh

theorem nested_grid_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (u : ℝ) :
    (∑ i, w i*(grid (ν i) s ((N : ℝ)*u)-grid (ν i) ((N : ℝ)*s) u)) ≤
      grid μ s ((N : ℝ)*u)-grid μ ((N : ℝ)*s) u := by
  classical
  obtain ⟨B,_,hB⟩ := hμ
  choose C hC hCi using hν
  let v := (N : ℝ)*u
  let a := Finset.Icc ⌊-B/s+v⌋ ⌊B/s+v⌋
  let ai := fun i => Finset.Icc ⌊-C i/s+v⌋ ⌊C i/s+v⌋
  let A := a ∪ Finset.univ.biUnion ai
  have ha : ∀ᵐ x ∂μ, label s v x ∈ A := (label_ae_finite μ hs hB).mono (fun x hx =>
    Finset.mem_union_left _ hx)
  have hai : ∀ i, ∀ᵐ x ∂ν i, label s v x ∈ A := by
    intro i
    filter_upwards [label_ae_finite (u := v) (ν i) hs (hCi i)] with x hx
    exact Finset.mem_union_right a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)
  have hh := entropy_coarsening_mixture μ ν w hw hm (label s v) (label_measurable s v)
    A ha hai (fun z : ℤ => z/(N : ℤ))
  have he : (fun z : ℤ => z/(N : ℤ)) ∘ label s v = label ((N : ℝ)*s) u := by
    funext x
    exact (label_nested s u x hN).symm
  rw [he] at hh
  exact hh

theorem grid_nsmul_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    IntervalIntegrable (fun u => grid μ s ((N : ℝ)*u)) volume 0 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simpa only [zero_div, div_self hn] using
    (grid_intervalIntegrable μ hμ hs 0 (N : ℝ)).comp_mul_left (c := (N : ℝ))

theorem averaged_nested_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    (∑ i, w i*(averaged (ν i) s-averaged (ν i) ((N : ℝ)*s))) ≤
      averaged μ s-averaged μ ((N : ℝ)*s) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := fun i => (grid_nsmul_intervalIntegrable (ν i) (hν i) hs hN).sub
    (grid_intervalIntegrable (ν i) (hν i) (mul_pos hn hs) 0 1)
  have hf := (grid_nsmul_intervalIntegrable μ hμ hs hN).sub
    (grid_intervalIntegrable μ hμ (mul_pos hn hs) 0 1)
  have hh := intervalIntegral.integral_mono zero_le_one (IntervalIntegrable.sum Finset.univ
    (fun i (_ : i ∈ Finset.univ) => (hi i).const_mul (w i))) hf
      (fun u => by
        simpa only [Finset.sum_apply] using nested_grid_mixture μ hμ ν hν w hw hm hs hN u)
  simp only [Finset.sum_apply] at hh
  rw [intervalIntegral.integral_finsetSum (fun i (_ : i ∈ Finset.univ) => (hi i).const_mul (w i))] at hh
  simp_rw [intervalIntegral.integral_const_mul] at hh
  simp_rw [intervalIntegral.integral_sub (grid_nsmul_intervalIntegrable (ν _) (hν _) hs hN)
    (grid_intervalIntegrable (ν _) (hν _) (mul_pos hn hs) 0 1),
    averaged_grid_nsmul (ν _) (hν _) hs hN, ← averaged_eq_intervalIntegral] at hh
  rw [intervalIntegral.integral_sub (grid_nsmul_intervalIntegrable μ hμ hs hN)
    (grid_intervalIntegrable μ hμ (mul_pos hn hs) 0 1),
    averaged_grid_nsmul μ hμ hs hN, ← averaged_eq_intervalIntegral] at hh
  exact hh

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_mixture.{uι} := @_root_.OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_mixture.{uι}
