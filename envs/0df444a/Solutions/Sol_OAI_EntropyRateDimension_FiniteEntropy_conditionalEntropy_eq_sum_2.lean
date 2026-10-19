-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:28:12.344009+00:00
-- url     : https://prove2.me/submissions/915e7c6a-dca1-47a5-8469-d77fd655c69b

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L347-L378
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_eq_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_normalize

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

theorem observableEntropy_equiv {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (e : β ≃ γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (e ∘ f) = observableEntropy s p f := by
  apply le_antisymm (observableEntropy_comp_le s p f e hp)
  have h := observableEntropy_comp_le s p (e ∘ f) e.symm hp
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using h

theorem observableEntropy_swap {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (fun a => (f a, g a)) =
      observableEntropy s p (fun a => (g a, f a)) := by
  exact (observableEntropy_equiv s p (fun a => (f a, g a)) (Equiv.prodComm β γ) hp).symm

theorem entropy_table_chain {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (p : α → β → ℝ) (hp : ∀ a ∈ s, ∀ b ∈ t, 0 ≤ p a b) :
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) =
      entropy s (fun a => ∑ b ∈ t, p a b) +
      ∑ a ∈ s, (∑ b ∈ t, p a b) * entropy t (fun b => p a b / ∑ c ∈ t, p a c) := by
  simp only [entropy, Finset.sum_product, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact entropy_normalize t (p a) (hp a ha)

theorem mass_filter_div {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (c : γ) (b : β) (P : ℝ) :
    mass (s.filter (fun a => g a = c)) (fun a => p a / P) f b =
      mass s p (fun a => (g a, f a)) (c, b) / P := by
  classical
  simp only [mass, ← Finset.sum_div, Finset.filter_filter, Prod.mk.injEq]

theorem conditionalEntropy_eq_sum {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p f g = ∑ c ∈ s.image g, mass s p g c *
      observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
  classical
  have hrect := observableEntropy_on_superset s (s.image g ×ˢ s.image f) p
    (fun a => (g a, f a)) (fun a ha => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem g ha, Finset.mem_image_of_mem f ha⟩)
  rw [entropy_table_chain (s.image g) (s.image f)
    (fun c b => mass s p (fun a => (g a, f a)) (c, b))
    (fun c _ b _ => mass_nonneg s p _ hp _)] at hrect
  simp only [mass_pair_fst] at hrect
  have hinner : ∀ c ∈ s.image g,
      entropy (s.image f) (fun b => mass s p (fun a => (g a, f a)) (c, b) / mass s p g c) =
      observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
    intro c _
    rw [observableEntropy_on_superset _ (s.image f) _ f]
    · apply Finset.sum_congr rfl
      intro b _
      rw [mass_filter_div]
    · intro a ha
      exact Finset.mem_image_of_mem f (Finset.mem_filter.mp ha).1
  have hh : observableEntropy s p (fun a => (g a, f a)) = observableEntropy s p g +
      ∑ c ∈ s.image g, mass s p g c *
        observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
    rw [hrect]
    congr 1
    apply Finset.sum_congr rfl
    intro c hc
    rw [hinner c hc]
  rw [conditionalEntropy, observableEntropy_swap s p f g hp, hh, add_sub_cancel_left]

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα,uβ,uγ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_eq_sum.{uα,uβ,uγ} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_eq_sum.{uα,uβ,uγ}
