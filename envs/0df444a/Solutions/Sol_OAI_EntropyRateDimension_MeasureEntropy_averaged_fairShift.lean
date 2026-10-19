-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.averaged_fairShift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:09:50.3954+00:00
-- url     : https://prove2.me/submissions/b728c170-91e0-4ff4-b09a-ca51e086504e

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L928-L968
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.averaged_fairShift. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_comp
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_fairShift

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

theorem label_nested (s u x : ℝ) {N : ℕ} (hN : 0 < N) :
    label ((N : ℝ)*s) u x = label s ((N : ℝ)*u) x / (N : ℤ) := by
  simp only [label]
  rw [← Int.floor_div_natCast]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [add_div, mul_div_cancel_left₀ u hn]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem entropy_summable {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    Summable (fun b => Real.negMulLog (mass μ f b)) := by
  apply summable_of_ne_finset_zero (s := a)
  intro b hb
  simp only [mass_eq_zero_of_ae μ f a ha hb, Real.negMulLog_zero]

theorem mass_summable {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    Summable (mass μ f) := by
  apply summable_of_ne_finset_zero (s := a)
  exact fun b hb => mass_eq_zero_of_ae μ f a ha hb

theorem mass_tsum {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    ∑' b, mass μ f b = 1 := by
  rw [tsum_eq_sum (fun b hb => mass_eq_zero_of_ae μ f a ha hb)]
  exact mass_sum μ f hf a ha

theorem CompactlyCarried.fairShift {μ : Measure ℝ} (hμ : CompactlyCarried μ) (v : ℝ) :
    CompactlyCarried (fairShift μ v) := by
  apply CompactlyCarried.mixture
  intro i
  simpa only [one_mul] using hμ.map_affine 1 ((i : ℝ)*v)

theorem mass_int_div_two {α : Type uα} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℤ) (hf : Measurable f) (k : ℤ) :
    mass μ (fun x => f x/2) k = mass μ f (2*k)+mass μ f (2*k+1) := by
  have he : {x | f x/2=k} = {x | f x=2*k} ∪ {x | f x=2*k+1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    omega
  unfold mass
  rw [he]
  apply measureReal_union
  · exact Set.disjoint_left.mpr (by
      intro x hx hy
      simp only [Set.mem_ofPred_eq] at hx hy
      omega)
  · exact measurableSet_eq_fun hf measurable_const
  · exact measure_ne_top μ _
  · exact measure_ne_top μ _

theorem mass_nested_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s u : ℝ) (k : ℤ) :
    mass μ (label (2*s) (u/2)) k =
      mass μ (label s u) (2*k)+mass μ (label s u) (2*k+1) := by
  have he : label (2*s) (u/2) = fun x => label s u x/2 := by
    funext x
    simpa only [Nat.cast_ofNat, show (2 : ℝ) * (u / 2) = u by ring] using
      label_nested s (u/2) x (by norm_num : 0 < (2 : ℕ))
  rw [he, mass_int_div_two μ _ (label_measurable s u)]

theorem mass_fairShift_odd (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (k : ℤ) :
    mass (fairShift μ s) (label s u) (2*k+1) =
      mass μ (label (2*s) (u/2)) k/2 := by
  rw [mass_fairShift μ hs, mass_nested_two]
  simp only [add_sub_cancel_right]
  ring

theorem mass_fairShift_even (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (k : ℤ) :
    mass (fairShift μ s) (label s u) (2*k) =
      mass μ (label (2*s) ((u+1)/2)) k/2 := by
  have he (j : ℤ) : mass μ (label s (u+1)) j = mass μ (label s u) (j-1) := by
    unfold mass label
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, ← add_assoc, Int.floor_add_one]
    omega
  rw [mass_fairShift μ hs, mass_nested_two, he, he]
  simp only [add_sub_cancel_right]
  ring

theorem entropy_half_mass {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    (∑' b, Real.negMulLog (mass μ f b/2)) = entropy μ f/2+Real.log 2/2 := by
  have he (b : β) : Real.negMulLog (mass μ f b/2) =
      (1/2)*Real.negMulLog (mass μ f b)+Real.negMulLog (1/2)*mass μ f b := by
    rw [div_eq_mul_inv, Real.negMulLog_mul]
    ring_nf
  simp_rw [he]
  rw [((entropy_summable μ f a ha).mul_left (1/2)).tsum_add
    ((mass_summable μ f a ha).mul_left (Real.negMulLog (1/2))),
    tsum_mul_left, tsum_mul_left, mass_tsum μ f hf a ha]
  have hc : Real.negMulLog (1/2)=Real.log 2/2 := by
    change -(1/2 : ℝ)*Real.log (1/2)=_
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hc]
  change (1/2)*entropy μ f+(Real.log 2/2)*1 = _
  ring

theorem grid_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    grid (fairShift μ s) s u = Real.log 2+
      (grid μ (2*s) (u/2)+grid μ (2*s) ((u+1)/2))/2 := by
  classical
  obtain ⟨B,hB,hBμ⟩ := (hμ.fairShift s)
  let F := fun j => Real.negMulLog (mass (fairShift μ s) (label s u) j)
  have hf : Summable F := entropy_summable (fairShift μ s) _ _ (label_ae_finite _ hs hBμ)
  have heven : Summable (fun k : ℤ => F (k*2)) := hf.comp_injective (i := fun k : ℤ => k*2) (by
    intro a b h
    change a*2=b*2 at h
    omega)
  have hodd : Summable (fun k : ℤ => F (k*2+1)) := hf.comp_injective (i := fun k : ℤ => k*2+1) (by
    intro a b h
    change a*2+1=b*2+1 at h
    omega)
  have hprod := ((Int.divModEquiv 2).symm.summable_iff).mpr hf
  change Summable (fun p => F ((Int.divModEquiv 2).symm p)) at hprod
  change (∑' j, F j) = _
  rw [← (Int.divModEquiv 2).symm.tsum_eq F, hprod.tsum_prod]
  simp only [tsum_fintype, Fin.sum_univ_two, Int.divModEquiv_symm_apply,
    Nat.cast_ofNat, Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_one, Nat.cast_one]
  rw [heven.tsum_add hodd]
  dsimp only [F]
  simp_rw [show ∀ k : ℤ, k*2=2*k from fun k => mul_comm k 2,
    mass_fairShift_even μ hs, mass_fairShift_odd μ hs]
  obtain ⟨C,hC,hCμ⟩ := hμ
  rw [entropy_half_mass μ _ (label_measurable _ _) _
      (label_ae_finite μ (by linarith : 0 < 2*s) hCμ),
    entropy_half_mass μ _ (label_measurable _ _) _
      (label_ae_finite μ (by linarith : 0 < 2*s) hCμ)]
  change grid μ (2*s) ((u+1)/2)/2+Real.log 2/2+
    (grid μ (2*s) (u/2)/2+Real.log 2/2) = _
  ring

theorem averaged_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    averaged (fairShift μ s) s = averaged μ (2*s)+Real.log 2 := by
  have ht : 0 < 2*s := by linarith
  let f := grid μ (2*s)
  have hi0 : IntervalIntegrable (fun u => f (u/2)) volume 0 1 := by
    have h := (grid_intervalIntegrable μ hμ ht 0 (1/2)).comp_mul_left (c := (1/2 : ℝ))
    norm_num at h
    simpa only [f, div_eq_mul_inv, mul_comm, one_mul] using h
  have hi1 : IntervalIntegrable (fun u => f ((u+1)/2)) volume 0 1 := by
    have h := (grid_intervalIntegrable μ hμ ht (1/2) 1).comp_mul_left (c := (1/2 : ℝ))
    norm_num at h
    have hh := h.comp_add_right 1
    norm_num at hh
    simpa only [f, div_eq_mul_inv, mul_comm, one_mul] using hh
  have he0 : (∫ u in (0 : ℝ)..1, f (u/2)) = 2*(∫u in (0 : ℝ)..(1/2), f u) := by
    rw [intervalIntegral.integral_comp_div f (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zero_div, smul_eq_mul]
  have he1 : (∫ u in (0 : ℝ)..1, f ((u+1)/2)) = 2*(∫u in (1/2 : ℝ)..1, f u) := by
    rw [intervalIntegral.integral_comp_add_right (fun u => f (u/2)) 1]
    norm_num only [zero_add, one_add_one_eq_two]
    rw [intervalIntegral.integral_comp_div f (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  rw [averaged_eq_intervalIntegral]
  calc
    _ = ∫u in (0 : ℝ)..1, Real.log 2+(f (u/2)+f ((u+1)/2))/2 := by
      apply intervalIntegral.integral_congr
      intro u _
      exact grid_fairShift μ hμ hs u
    _ = Real.log 2+(2*(∫u in (0 : ℝ)..(1/2), f u)+
        2*(∫u in (1/2 : ℝ)..1, f u))/2 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const ((hi0.add hi1).div_const 2),
        intervalIntegral.integral_div, intervalIntegral.integral_add hi0 hi1, he0, he1]
      simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    _ = averaged μ (2*s)+Real.log 2 := by
      have hh := intervalIntegral.integral_add_adjacent_intervals
        (grid_intervalIntegrable μ hμ ht 0 (1/2)) (grid_intervalIntegrable μ hμ ht (1/2) 1)
      change (∫u in (0 : ℝ)..(1/2), f u)+(∫u in (1/2 : ℝ)..1, f u) = _ at hh
      rw [← mul_add, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), hh,
        ← averaged_eq_intervalIntegral]
      ring

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.averaged_fairShift := @_root_.OAI.EntropyRateDimension.MeasureEntropy.averaged_fairShift
