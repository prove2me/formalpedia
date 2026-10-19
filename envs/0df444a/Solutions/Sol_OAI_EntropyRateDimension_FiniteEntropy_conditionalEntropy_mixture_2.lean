-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:44:20.178418+00:00
-- url     : https://prove2.me/submissions/060714eb-b98c-4d5e-8a91-726c4cb1935d

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L837-L865
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_mixture. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_condition_le
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_observableEntropy_mixture_joint
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_observableEntropy_mixture_marginal

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

theorem observableEntropy_equiv {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (e : β ≃ γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (e ∘ f) = observableEntropy s p f := by
  apply le_antisymm (observableEntropy_comp_le s p f e hp)
  have h := observableEntropy_comp_le s p (e ∘ f) e.symm hp
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using h

theorem conditionalEntropy_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) (g : α → γ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hp : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ p i a)
    (hp1 : ∀ i ∈ t, ∑ a ∈ s, p i a = 1) :
    (∑ i ∈ t, w i*conditionalEntropy s (p i) f g) ≤
      conditionalEntropy s (fun a => ∑ i ∈ t, w i*p i a) f g := by
  classical
  let q : ι × α → ℝ := fun ia => w ia.1*p ia.1 ia.2
  have hq : ∀ x ∈ t ×ˢ s, 0 ≤ q x := by
    intro x hx
    exact mul_nonneg (hw x.1 (Finset.mem_product.mp hx).1)
      (hp x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2)
  have hh := conditionalEntropy_condition_le (t ×ˢ s) q
    (fun ia => f ia.2) (fun ia => g ia.2) Prod.fst hq
  have he : observableEntropy (t ×ˢ s) q (fun x => (f x.2,(x.1,g x.2))) =
      observableEntropy (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) := by
    let e : ι × (β × γ) ≃ β × (ι × γ) :=
      { toFun := fun x => (x.2.1,(x.1,x.2.2))
        invFun := fun x => (x.2.1,(x.1,x.2.2))
        left_inv := by rintro ⟨i,b,c⟩; rfl
        right_inv := by rintro ⟨b,i,c⟩; rfl }
    exact observableEntropy_equiv (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) e hq
  dsimp only [conditionalEntropy] at hh ⊢
  rw [he, observableEntropy_mixture_joint t s w p (fun a => (f a,g a)) hp1,
    observableEntropy_mixture_joint t s w p g hp1,
    observableEntropy_mixture_marginal t s w p (fun a => (f a,g a)),
    observableEntropy_mixture_marginal t s w p g] at hh
  simpa only [mul_sub, Finset.sum_sub_distrib, add_sub_add_left_eq_sub] using hh

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι,uα,uβ,uγ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_mixture.{uι,uα,uβ,uγ} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_mixture.{uι,uα,uβ,uγ}
