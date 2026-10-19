-- Prove2me | solution 2 for OAI.EntropyRateDimension.ProductLaw.observable_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:40:37.927151+00:00
-- url     : https://prove2.me/submissions/acfa61f7-8554-4497-a3cc-74cade98f9e6

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/ProductLaw.lean:L157-L198
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.ProductLaw.observable_entropy. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_ProductLaw_entropy

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

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.ProductLaw ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace ProductLaw

variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]

omit [Fintype α] [DecidableEq ι] in
theorem weight_nonneg (p : ι → α → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : ι → α) :
    0 ≤ weight p x := Finset.prod_nonneg (fun i _ => hp i (x i))

variable {β : Type uβ} [DecidableEq β]

theorem mass_cells (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) :
    FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c =
      ∏ i, cellMass p g c i := by
  classical
  have hh := (Fintype.prod_sum (fun i a => if g i a = c i then p i a else 0)).symm
  simpa only [Fintype.prod_ite_zero, ← funext_iff, FiniteEntropy.mass,
    Finset.sum_filter, weight, cellMass] using hh

theorem observable_entropy [Nonempty α] [Nonempty β]
    (p : α → ℝ) (g : α → β) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g (x i)) =
      Fintype.card ι * FiniteEntropy.observableEntropy Finset.univ p g := by
  classical
  let B : Finset β := Finset.univ.image g
  let g' : α → B := fun a => ⟨g a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  have : Nonempty B := ⟨g' (Classical.choice inferInstance)⟩
  have hg : FiniteEntropy.observableEntropy Finset.univ p g =
      FiniteEntropy.observableEntropy Finset.univ p g' := by
    apply FiniteEntropy.observableEntropy_eq_of_fibers _ _ _ _ (fun a _ => hp a)
    intro a _ b _
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hG : FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g (x i)) =
      FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g' (x i)) := by
    apply FiniteEntropy.observableEntropy_eq_of_fibers _ _ _ _
      (fun x _ => weight_nonneg _ (fun _ a => hp a) x)
    intro x _ y _
    constructor
    · intro h
      funext i
      exact Subtype.ext (congrFun h i)
    · intro h
      funext i
      exact congrArg Subtype.val (congrFun h i)
  rw [hg, hG, FiniteEntropy.observableEntropy_on_superset Finset.univ Finset.univ _ _
    (fun _ _ => Finset.mem_univ _)]
  have hm : FiniteEntropy.mass Finset.univ (weight (fun _ : ι => p)) (fun x i => g' (x i)) =
      weight (fun _ : ι => FiniteEntropy.mass Finset.univ p g') := by
    funext c
    rw [mass_cells]
    simp only [weight, cellMass, FiniteEntropy.mass, Finset.sum_filter]
  have hpB : ∑ b : B, FiniteEntropy.mass Finset.univ p g' b = 1 := by
    rw [← hp1, ← FiniteEntropy.mass_sum Finset.univ p g']
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b _ hb
    exact FiniteEntropy.mass_eq_zero_of_not_mem _ _ _ hb
  rw [hm, entropy _ (fun _ => hpB)]
  rw [FiniteEntropy.observableEntropy_on_superset Finset.univ Finset.univ p g'
    (fun _ _ => Finset.mem_univ _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end ProductLaw

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.ProductLaw
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι,uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.ProductLaw.observable_entropy.{uι,uα,uβ} := @_root_.OAI.EntropyRateDimension.ProductLaw.observable_entropy.{uι,uα,uβ}
