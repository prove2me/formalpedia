-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.retained_loss_linear
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:45:56.297854+00:00
-- url     : https://prove2.me/submissions/f01a8a78-e558-4198-a91e-524713f2cf5e

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/RetainedLoss.lean:L100-L133
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.retained_loss_linear. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_eq_sum
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_le_log_card
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_grid_le_grid_add_log
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_comp
import Theorems.Thm_OAI_EntropyRateDimension_System_depth_bad_mass_bound
import Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_compact
import Theorems.Thm_OAI_EntropyRateDimension_Typed_entropyLoss_le
import Theorems.Thm_OAI_EntropyRateDimension_Typed_expected_grid_upper

-- ---- from OAI.MeasureTheory.SelfSimilar.Basic ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem mapMass_nonneg (S : System ι) (n : ℕ) (g : ℝ × ℝ) :
    0 ≤ S.mapMass n g := by
  classical
  exact Finset.sum_nonneg (fun w _ => (S.wordWeight_pos w).le)

theorem mapMass_le_one (S : System ι) (n : ℕ) (g : ℝ × ℝ) :
    S.mapMass n g ≤ 1 := by
  classical
  rw [mapMass, ← S.wordWeight_sum n]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun w _ _ => (S.wordWeight_pos w).le)

theorem walkEntropy_nonneg (S : System ι) (n : ℕ) : 0 ≤ S.walkEntropy n := by
  apply div_nonneg _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  apply Finset.sum_nonneg
  intro g _
  exact Real.negMulLog_nonneg (S.mapMass_nonneg n g) (S.mapMass_le_one n g)

theorem entropyRate_le (S : System ι) (n : ℕ) :
    S.entropyRate ≤ S.walkEntropy (n + 1) / (n + 1 : ℕ) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact div_nonneg (S.walkEntropy_nonneg _) (by positivity)
  · exact ⟨n, rfl⟩

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end System

end EntropyRateDimension
end

end OAI

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

theorem observableEntropy_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) : observableEntropy s p f = entropy t (mass s p f) := by
  classical
  apply Finset.sum_subset
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hf a ha
  · intro b _ hb
    rw [mass_eq_zero_of_not_mem s p f hb, Real.negMulLog_zero]

theorem observableEntropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (g ∘ f) ≤ observableEntropy s p f := by
  rw [observableEntropy_comp]
  exact observableEntropy_le _ _ _ (fun b _ => mass_nonneg s p f hp b)

theorem observableEntropy_le_log_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p f ≤ Real.log t.card := by
  rw [observableEntropy_on_superset s t p f hf]
  apply entropy_le_log_card _ _ (fun b _ => mass_nonneg s p f hp b)
  have h := sum_mass_mul s t p f (fun _ => 1) hf
  simpa only [mul_one, hp1] using h

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

theorem grid_le_grid_add_log_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t ≤ s) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log 2 := by
  have hc : ⌈t/s⌉ = (1 : ℤ) := by
    have hh := Int.ceil_pos.mpr (div_pos ht hs)
    have hu : ⌈t/s⌉ ≤ (1 : ℤ) := Int.ceil_le.mpr (by
      norm_num
      exact (div_le_one hs).mpr hts)
    omega
  simpa only [hc, Int.cast_one, one_add_one_eq_two] using grid_le_grid_add_log μ hμ hs ht u v

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.WordTypes ----
namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace System
variable {ι : Type uι} [Fintype ι]

theorem map_entropy_as_observation (S : System ι) (n : ℕ) :
    FiniteEntropy.observableEntropy Finset.univ (S.wordWeight (n := n)) S.completeMap =
      S.walkEntropy n*Real.log 2 := by
  classical
  unfold walkEntropy FiniteEntropy.observableEntropy FiniteEntropy.entropy mapSupport
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ)<2)))]
  rfl

end System
end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Conditioning ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ

namespace EntropyRateDimension.FairPairs
open MeasureTheory FiniteEntropy
open scoped BigOperators ENNReal

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.FiniteCondition
open FiniteEntropy FairPairs MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem law_entropy_mean (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (f : α → ℝ) :
    (∑ a, p a*(law p hp tag a f).shannonEntropy)*Real.log 2=
      FiniteEntropy.conditionalEntropy Finset.univ p f tag := by
  classical
  simp only [law,Law.ofObservable_entropy,← mul_div_assoc,← Finset.sum_div,
    div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne']
  rw [conditionalEntropy_eq_sum _ _ _ _ (fun a _ => (hp a).le)]
  symm
  convert FiniteEntropy.sum_mass_mul Finset.univ (Finset.univ.image tag) p tag
    (fun c => observableEntropy (Finset.univ.filter (fun a => tag a=c))
      (fun a => p a/FiniteEntropy.mass Finset.univ p tag c) f)
    (fun a ha => Finset.mem_image_of_mem tag ha) using 1
  rfl

end EntropyRateDimension.FiniteCondition

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.EntropyBudget ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open FiniteEntropy FairPairs FiniteCondition MeasureEntropy MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] [DecidableEq β]

theorem expected_entropy_lower (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v) (n : ℕ) :
    S.walkEntropy n*Real.log 2-(n : ℝ)*Real.log (Fintype.card β) ≤
      (∑ w : Fin n → α, S.wordWeight w*(law S tag w).shannonEntropy)*Real.log 2 := by
  classical
  rw [show (∑ w : Fin n → α, S.wordWeight w*(law S tag w).shannonEntropy)*Real.log 2=
    conditionalEntropy Finset.univ S.wordWeight (fun w => (S.completeMap w).2) (tagWord tag) from
      law_entropy_mean S.wordWeight S.wordWeight_pos (tagWord tag) _]
  have he := observableEntropy_le_of_fibers Finset.univ (S.wordWeight (n := n))
    S.completeMap (fun w => ((S.completeMap w).2,tagWord tag w))
    (fun w _ => (S.wordWeight_pos w).le) (by
      intro w _ v _ h
      apply Prod.ext
      · rw [S.completeMap_slope,S.completeMap_slope]
        exact Finset.prod_congr rfl (fun j _ => hr _ _ (congrFun (Prod.mk.inj h).2 j))
      · exact (Prod.mk.inj h).1)
  have ht := observableEntropy_le_log_on_superset Finset.univ Finset.univ
    (S.wordWeight (n := n)) (tagWord tag) (fun _ _ => Finset.mem_univ _)
    (fun w _ => (S.wordWeight_pos w).le) (S.wordWeight_sum n)
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow] at ht
  rw [S.map_entropy_as_observation] at he
  unfold conditionalEntropy
  linarith

theorem expected_entropyLoss_lower (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    S.walkEntropy n*Real.log 2-(n : ℝ)*Real.log (Fintype.card β)-grid μ ρ 0-Real.log 2 ≤
      ∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w ρ := by
  have he := expected_entropy_lower S tag hr n
  have hg := expected_grid_upper S tag hr μ hμ hc n hρ
  have hid : (∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w ρ)=
      (∑ w : Fin n → α, S.wordWeight w*(law S tag w).shannonEntropy)*Real.log 2-
      (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 := by
    simp only [entropyLoss,mul_sub,sub_mul,← mul_assoc,Finset.sum_sub_distrib,Finset.sum_mul]
  rw [hid]
  linarith

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.RetainedLoss ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory

theorem grid_le_averaged_add_log_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    grid μ s u ≤ averaged μ s+Real.log 2 := by
  have hh := intervalIntegral.integral_mono zero_le_one
    (intervalIntegrable_const (c := grid μ s u))
    ((grid_intervalIntegrable μ hμ hs 0 1).add intervalIntegrable_const)
    (fun v => grid_le_grid_add_log_two μ hμ hs hs le_rfl u v)
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add
    (grid_intervalIntegrable μ hμ hs 0 1) intervalIntegrable_const,
    intervalIntegral.integral_const,← averaged_eq_intervalIntegral] at hh
  simpa only [sub_zero,one_smul] using hh

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.Typed
open FairPairs MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]

theorem fineScale_pos (A : ℝ) (n : ℕ) : 0 < fineScale A n := zpow_pos (by norm_num) _

theorem fineScale_lt_one {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n) : fineScale A n < 1 := by
  have ht : 0 < ⌈A*n⌉ := Int.ceil_pos.mpr (mul_pos hA (by exact_mod_cast hn))
  change (2 : ℝ)^(-⌈A*n⌉) < (2 : ℝ)^(0 : ℤ)
  exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)

theorem fineScale_log (A : ℝ) (n : ℕ) :
    Real.log (1/fineScale A n)=(⌈A*n⌉ : ℝ)*Real.log 2 := by
  rw [one_div,Real.log_inv,fineScale,Real.log_zpow,Int.cast_neg,neg_mul,neg_neg]

theorem expected_loss_linear (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {D C A : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C)
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ)*(S.entropyRate*Real.log 2-Real.log (Fintype.card β)-D*A*Real.log 2)-
        (D*Real.log 2+C+2*Real.log 2) ≤
      ∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w (fineScale A n) := by
  obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ
  have hc' : CompactlyCarried μ := ⟨B,hB.le,hc⟩
  have he := expected_entropyLoss_lower S tag hr μ hμ hc' n (fineScale_pos A n)
  have hg : grid μ (fineScale A n) 0 ≤ D*Real.log (1/fineScale A n)+C+Real.log 2 := by
    have h1 := grid_le_averaged_add_log_two μ hc' (fineScale_pos A n) 0
    have h2 := hb _ (fineScale_pos A n) (fineScale_lt_one hA hn)
    linarith
  rw [fineScale_log] at hg
  have hh := S.entropyRate_le (n-1)
  rw [Nat.sub_add_cancel hn] at hh
  have hh' := mul_le_mul_of_nonneg_right
    ((le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ)<n)).mp hh)
    (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
  have hhceil := mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one (A*n)).le
    (mul_nonneg hD (Real.log_pos (by norm_num : (1 : ℝ)<2)).le)
  nlinarith

omit [Fintype β] in
theorem discarded_loss_bound (S : System α) (tag : α → β)
    {A' : ℝ} (hA' : S.lyapunov < A') {n : ℕ} (hn : 0 < n) (ρ : ℝ) :
    (∑ w : Fin n → α, if A'*n < S.wordDepth w then
      S.wordWeight w*entropyLoss S tag w ρ else 0) ≤
        Real.log (Fintype.card α)*S.depthVariance/(A'-S.lyapunov)^2 := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hcard : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hl : 0 ≤ Real.log (Fintype.card α) := Real.log_nonneg hcard
  have hbound := S.depth_bad_mass_bound hA' hn
  calc
    _ ≤ (n : ℝ)*Real.log (Fintype.card α)*
        ∑ w : Fin n → α, if A'*n < S.wordDepth w then S.wordWeight w else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left (entropyLoss_le S tag w ρ) (S.wordWeight_pos w).le
      · simp
    _ ≤ (n : ℝ)*Real.log (Fintype.card α)*
        (S.depthVariance/((n : ℝ)*(A'-S.lyapunov)^2)) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg hnR.le hl)
    _ = _ := by field_simp

theorem retained_loss_linear (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {D C A A' : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (hA' : S.lyapunov < A')
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C)
    (hgap : D*A*Real.log 2 < S.entropyRate*Real.log 2-Real.log (Fintype.card β)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      ε*n ≤ retainedLoss S tag A A' n := by
  classical
  let γ := S.entropyRate*Real.log 2-Real.log (Fintype.card β)-D*A*Real.log 2
  have hγ : 0 < γ := sub_pos.mpr hgap
  let K := D*Real.log 2+C+2*Real.log 2+
    Real.log (Fintype.card α)*S.depthVariance/(A'-S.lyapunov)^2
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*K/γ))
  have hNpos : 0 < N := by
    have := (le_max_left _ _).trans_lt hN
    exact_mod_cast (lt_trans zero_lt_one this)
  refine ⟨γ/2,by positivity,N,hNpos,fun n hn => ?_⟩
  have hn0 := hNpos.trans_le hn
  have he := expected_loss_linear S tag hr μ hμ hD hA hb hn0
  have hd := discarded_loss_bound S tag hA' hn0 (fineScale A n)
  have hid : retainedLoss S tag A A' n+
      (∑ w : Fin n → α, if A'*n < S.wordDepth w then
        S.wordWeight w*entropyLoss S tag w (fineScale A n) else 0)=
      ∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w (fineScale A n) := by
    rw [retainedLoss,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : S.wordDepth w ≤ A'*n <;> simp [h,not_lt_of_ge,lt_of_not_ge]
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hNK := (div_lt_iff₀ hγ).mp ((le_max_right _ _).trans_lt hN)
  change (n : ℝ)*γ-(D*Real.log 2+C+2*Real.log 2) ≤ _ at he
  dsimp only [K] at hNK
  nlinarith

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open FairPairs MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.retained_loss_linear.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.retained_loss_linear.{uα,uβ}
