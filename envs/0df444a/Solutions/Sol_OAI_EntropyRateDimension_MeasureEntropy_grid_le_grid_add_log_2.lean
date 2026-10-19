-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.grid_le_grid_add_log
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:59:33.056929+00:00
-- url     : https://prove2.me/submissions/054d2313-f3cd-41a8-876b-eb838c0a6078

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L486-L504
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.grid_le_grid_add_log. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_le_log_card
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_normalize
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

theorem entropy_mixture {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (w : β → ℝ) (p : β → α → ℝ)
    (hw : ∀ b ∈ t, 0 ≤ w b) (hw1 : ∑ b ∈ t, w b = 1)
    (hp : ∀ b ∈ t, ∀ a ∈ s, 0 ≤ p b a) :
    ∑ b ∈ t, w b * entropy s (p b) ≤
      entropy s (fun a => ∑ b ∈ t, w b * p b a) := by
  simp only [entropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  exact Real.concaveOn_negMulLog.le_map_sum hw hw1 (fun b hb => hp b hb a ha)

theorem entropy_joint_le {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (p : α → β → ℝ) (hp : ∀ a ∈ s, ∀ b ∈ t, 0 ≤ p a b)
    (hp1 : ∑ a ∈ s, ∑ b ∈ t, p a b = 1) :
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) ≤
      entropy s (fun a => ∑ b ∈ t, p a b) + entropy t (fun b => ∑ a ∈ s, p a b) := by
  let r := fun a => ∑ b ∈ t, p a b
  have hr : ∀ a ∈ s, 0 ≤ r a := fun a ha => Finset.sum_nonneg (hp a ha)
  have hterm : ∀ a ∈ s, ∀ b ∈ t, r a * (p a b / r a) = p a b := by
    intro a ha b hb
    by_cases h : r a = 0
    · have hl := Finset.single_le_sum (hp a ha) hb
      have hz : p a b = 0 := le_antisymm (h ▸ hl) (hp a ha b hb)
      simp [hz]
    · exact mul_div_cancel₀ _ h
  have hc := entropy_mixture t s r (fun a b => p a b / r a) hr hp1
    (fun a ha b hb => div_nonneg (hp a ha b hb) (hr a ha))
  have hmix : entropy t (fun b => ∑ a ∈ s, r a * (p a b / r a)) =
      entropy t (fun b => ∑ a ∈ s, p a b) := by
    apply Finset.sum_congr rfl
    intro b hb
    congr 1
    exact Finset.sum_congr rfl (fun a ha => hterm a ha b hb)
  rw [hmix] at hc
  calc
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) =
        ∑ a ∈ s, entropy t (p a) := by simp only [entropy, Finset.sum_product]
    _ = entropy s r + ∑ a ∈ s, r a * entropy t (fun b => p a b / r a) := by
      simp only [entropy, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      exact entropy_normalize t (p a) (hp a ha)
    _ ≤ _ := add_le_add le_rfl hc

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

theorem mass_pair_fst {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (b : β) :
    ∑ c ∈ s.image g, mass s p (fun a => (f a, g a)) (b, c) = mass s p f b := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hg : g a ∈ s.image g := Finset.mem_image_of_mem g ha
  by_cases hf : f a = b
  · simp [hf, hg]
  · simp [hf]

theorem mass_pair_snd {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (c : γ) :
    ∑ b ∈ s.image f, mass s p (fun a => (f a, g a)) (b, c) = mass s p g c := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hf : f a ∈ s.image f := Finset.mem_image_of_mem f ha
  by_cases hg : g a = c
  · simp [hg, hf]
  · simp [hg]

theorem observableEntropy_pair_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p (fun a => (f a, g a)) ≤
      observableEntropy s p f + observableEntropy s p g := by
  classical
  rw [observableEntropy_on_superset s (s.image f ×ˢ s.image g) p _
    (fun a ha => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem f ha, Finset.mem_image_of_mem g ha⟩)]
  have h := entropy_joint_le (s.image f) (s.image g)
    (fun b c => mass s p (fun a => (f a, g a)) (b, c))
    (fun b _ c _ => mass_nonneg s p _ hp _) ?_
  · simpa only [mass_pair_fst, mass_pair_snd, observableEntropy] using h
  · simpa only [mass_pair_fst, mass_sum] using hp1

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

theorem entropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) :
    entropy μ (g ∘ f) ≤ entropy μ f := by
  rw [entropy_comp μ f hf s hs g, entropy_eq_sum μ f s hs]
  exact FiniteEntropy.observableEntropy_le s _ g (fun b _ => mass_nonneg μ f b)

theorem entropy_pair_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    [DecidableEq β] [DecidableEq γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f)
    (g : α → γ) (hg : Measurable g) (s : Finset β) (t : Finset γ)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂μ, g x ∈ t) :
    entropy μ (fun x => (f x,g x)) ≤ entropy μ f + entropy μ g := by
  classical
  let F := fun x => (f x,g x)
  have hF : Measurable F := hf.prodMk hg
  have hst : ∀ᵐ x ∂μ, F x ∈ s ×ˢ t := by
    filter_upwards [hs,ht] with x hx hy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  have h := FiniteEntropy.observableEntropy_pair_le (s ×ˢ t) (mass μ F) Prod.fst Prod.snd
    (fun b _ => mass_nonneg μ F b) (mass_sum μ F hF (s ×ˢ t) hst)
  have hid : (fun b : β × γ => (b.1,b.2)) = id := rfl
  rw [hid, FiniteEntropy.observableEntropy_id] at h
  have hfst := entropy_comp μ F hF (s ×ˢ t) hst Prod.fst
  have hsnd := entropy_comp μ F hF (s ×ˢ t) hst Prod.snd
  change entropy μ f = _ at hfst
  change entropy μ g = _ at hsnd
  rw [hfst, hsnd, entropy_eq_sum μ F (s ×ˢ t) hst]
  exact h

theorem entropy_congr_ae {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    (μ : Measure α) {f g : α → β} (h : f =ᵐ[μ] g) : entropy μ f = entropy μ g := by
  apply tsum_congr
  intro b
  congr 1
  apply measureReal_congr
  filter_upwards [h] with x hx
  exact congrArg (fun y => y = b) hx

theorem entropy_le_add_of_reconstruct {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → δ) (g : α → β) (h : α → γ)
    (hg : Measurable g) (hh : Measurable h) (s : Finset β) (t : Finset γ)
    (hs : ∀ᵐ x ∂μ, g x ∈ s) (ht : ∀ᵐ x ∂μ, h x ∈ t)
    (q : β × γ → δ) (hq : ∀ᵐ x ∂μ, f x = q (g x,h x)) :
    entropy μ f ≤ entropy μ g + entropy μ h := by
  have hst : ∀ᵐ x ∂μ, (g x,h x) ∈ s ×ˢ t := by
    filter_upwards [hs,ht] with x hx hy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  calc
    entropy μ f = entropy μ (q ∘ fun x => (g x,h x)) := entropy_congr_ae μ hq
    _ ≤ entropy μ (fun x => (g x,h x)) := entropy_comp_le μ _ (hg.prodMk hh) _ hst q
    _ ≤ entropy μ g + entropy μ h := entropy_pair_le μ g hg h hh s t hs ht

theorem entropy_le_log_card {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f ≤ Real.log s.card := by
  rw [entropy_eq_sum μ f s hs]
  exact FiniteEntropy.entropy_le_log_card s _ (fun b _ => mass_nonneg μ f b)
    (mass_sum μ f hf s hs)

theorem relativeLabel_measurable (s t u v : ℝ) : Measurable (relativeLabel s t u v) := by
  unfold relativeLabel
  exact (label_measurable s u).sub
    (((((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp (label_measurable t v)).const_mul (t/s)).add_const u).sub_const ((t/s)*v)).floor

theorem grid_le_grid_add_log (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log (⌈t/s⌉+1 : ℝ) := by
  obtain ⟨B,_,hB⟩ := hμ
  have hrel : ∀ᵐ x ∂μ, relativeLabel s t u v x ∈ Finset.Icc (0 : ℤ) ⌈t/s⌉ :=
    Filter.Eventually.of_forall (relativeLabel_mem hs ht u v)
  have he := entropy_le_add_of_reconstruct μ (label s u) (label t v) (relativeLabel s t u v)
    (label_measurable t v) (relativeLabel_measurable s t u v) _ _
    (label_ae_finite μ ht hB) hrel
    (fun p : ℤ × ℤ => ⌊(t/s)*(p.1 : ℝ)+u-(t/s)*v⌋+p.2)
    (Filter.Eventually.of_forall (fun x => by dsimp [relativeLabel]; omega))
  have hc := entropy_le_log_card μ _ (relativeLabel_measurable s t u v) _ hrel
  have hn : 0 ≤ ⌈t/s⌉+1 := by have hh := (Int.ceil_pos.mpr (div_pos ht hs)); omega
  have hcard : ((Finset.Icc (0 : ℤ) ⌈t/s⌉).card : ℝ) = (⌈t/s⌉ : ℝ)+1 := by
    rw [Int.card_Icc]
    have he := congrArg (fun k : ℤ => (k : ℝ)) (Int.toNat_of_nonneg hn)
    simpa only [sub_zero, Int.cast_natCast, Int.cast_add, Int.cast_one] using he
  rw [hcard] at hc
  exact he.trans (add_le_add_right hc _)

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.grid_le_grid_add_log := @_root_.OAI.EntropyRateDimension.MeasureEntropy.grid_le_grid_add_log
