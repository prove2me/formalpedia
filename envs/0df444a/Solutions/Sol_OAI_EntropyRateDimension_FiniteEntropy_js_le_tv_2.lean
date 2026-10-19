-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.js_le_tv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:47:21.034037+00:00
-- url     : https://prove2.me/submissions/d945cda1-ed95-4d9f-8c06-fd960e7df661

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L1101-L1127
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.js_le_tv. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_condition_le
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_observableEntropy_mixture_joint
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_observableEntropy_mixture_joint_general
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

theorem conditionalEntropy_nonneg {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) : 0 ≤ conditionalEntropy s p f g := by
  apply sub_nonneg.mpr
  exact observableEntropy_comp_le s p (fun a => (f a, g a)) Prod.snd hp

theorem observableEntropy_equiv {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (e : β ≃ γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (e ∘ f) = observableEntropy s p f := by
  apply le_antisymm (observableEntropy_comp_le s p f e hp)
  have h := observableEntropy_comp_le s p (e ∘ f) e.symm hp
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using h

theorem observableEntropy_id {α : Type uα} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) : observableEntropy s p id = entropy s p := by
  simp only [observableEntropy, Finset.image_id, entropy, mass, id_eq]
  apply Finset.sum_congr rfl
  intro a ha
  simp [Finset.filter_eq',ha]

theorem conditionalEntropy_mixture_general {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) (g : α → γ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hp : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ p i a)
    :
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
  rw [he, observableEntropy_mixture_joint_general t s w p (fun a => (f a,g a)),
    observableEntropy_mixture_joint_general t s w p g,
    observableEntropy_mixture_marginal t s w p (fun a => (f a,g a)),
    observableEntropy_mixture_marginal t s w p g] at hh
  simpa only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, add_sub_add_left_eq_sub] using hh

theorem conditionalEntropy_mono {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p q : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hpq : ∀ a ∈ s, p a ≤ q a) :
    conditionalEntropy s p f g ≤ conditionalEntropy s q f g := by
  let P : Bool → α → ℝ := fun b => if b then p else fun a => q a-p a
  have hh := conditionalEntropy_mixture_general Finset.univ s (fun _ : Bool => (1 : ℝ))
    P f g (by intros; exact zero_le_one) (by
      intro b _ a ha
      cases b
      · exact sub_nonneg.mpr (hpq a ha)
      · exact hp a ha)
  have he : (fun a => ∑ b : Bool, (1 : ℝ)*P b a)=q := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte, one_mul]
    ring
  rw [he] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte, one_mul] at hh
  have hn := conditionalEntropy_nonneg s (fun a => q a-p a) f g
    (fun a ha => sub_nonneg.mpr (hpq a ha))
  linarith

theorem mixture_information_common {ι : Type uι} {α : Type uα} [DecidableEq ι] [DecidableEq α]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (r : α → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i=1)
    (hp1 : ∀ i ∈ t, ∑ a ∈ s, p i a=1)
    (hr : ∀ a ∈ s, 0 ≤ r a) (hrp : ∀ i ∈ t, ∀ a ∈ s, r a ≤ p i a) :
    entropy s (fun a => ∑ i ∈ t, w i*p i a) - (∑ i ∈ t, w i*entropy s (p i)) ≤
      (1-∑ a ∈ s, r a)*entropy t w := by
  have hh := conditionalEntropy_mono (t ×ˢ s)
    (fun ia => w ia.1*r ia.2) (fun ia => w ia.1*p ia.1 ia.2) Prod.fst Prod.snd
    (by
      intro x hx
      exact mul_nonneg (hw x.1 (Finset.mem_product.mp hx).1)
        (hr x.2 (Finset.mem_product.mp hx).2))
    (by
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (hrp x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2)
        (hw x.1 (Finset.mem_product.mp hx).1))
  dsimp only [conditionalEntropy] at hh
  have hjr := observableEntropy_mixture_joint_general t s w (fun _ => r) id
  have hjp := observableEntropy_mixture_joint t s w p id hp1
  have hmr := observableEntropy_mixture_marginal t s w (fun _ => r) id
  have hmp := observableEntropy_mixture_marginal t s w p id
  simp only [id_eq] at hjr hjp hmr hmp
  rw [hjr, hjp, hmr, hmp] at hh
  simp_rw [observableEntropy_id, ← Finset.sum_mul, hw1, one_mul] at hh
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hw1, one_mul] at hh
  change (∑ a ∈ s, r a)*entropy t w+entropy s r-entropy s r ≤
    entropy t w+(∑ i ∈ t, w i*entropy s (p i))-
      entropy s (fun a => ∑ i ∈ t, w i*p i a) at hh
  nlinarith

theorem sum_min_eq_one_sub_tv {α : Type uα} (s : Finset α) (p q : α → ℝ)
    (hp1 : ∑ a ∈ s, p a=1) (hq1 : ∑ a ∈ s, q a=1) :
    (∑ a ∈ s, min (p a) (q a))=1-totalVariation s p q := by
  have he (a : α) : min (p a) (q a)=(p a+q a-|p a-q a|)/2 := by
    rcases le_total (p a) (q a) with h|h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp1, hq1]
  unfold totalVariation
  ring

theorem js_le_tv {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) :
    js s p q ≤ totalVariation s p q*Real.log 2 := by
  let P : Bool → α → ℝ := fun b => if b then p else q
  have hh := mixture_information_common Finset.univ s (fun _ : Bool => (1/2 : ℝ))
    P (fun a => min (p a) (q a)) (by intros; positivity)
    (by norm_num [Fintype.sum_bool]) (by intro b _; cases b <;> assumption)
    (fun a ha => le_min (hp a ha) (hq a ha)) (by
      intro b _ a _
      cases b
      · exact min_le_right _ _
      · exact min_le_left _ _)
  have he : (fun a => ∑ b : Bool, (1/2 : ℝ)*P b a)=fun a => (p a+q a)/2 := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [he, sum_min_eq_one_sub_tv s p q hp1 hq1] at hh
  have hb : entropy Finset.univ (fun _ : Bool => (1/2 : ℝ))=Real.log 2 := by
    simp only [entropy, Fintype.sum_bool]
    change -(1/2 : ℝ)*Real.log (1/2)+(-(1/2 : ℝ)*Real.log (1/2))=_
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hb] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte] at hh
  unfold js
  linarith

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.js_le_tv.{uα} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.js_le_tv.{uα}
