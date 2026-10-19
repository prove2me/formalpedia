-- Prove2me | solution 1 for OAI.EntropyRateDimension.FairPairs.pair_bound_natural
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:55:49.570012+00:00
-- url     : https://prove2.me/submissions/3b173e6e-64dc-4209-8673-ff690b4507fc

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/SumsetBound.lean:L273-L325
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FairPairs.pair_bound_natural. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_FairPairs_coupling_distance_le
import Theorems.Thm_OAI_EntropyRateDimension_FairPairs_sum_refinementCost_le
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_le_log_card
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_normalize
import Theorems.Thm_OAI_EntropyRateDimension_FiniteRefinement_exists_entropy_step
import Theorems.Thm_OAI_EntropyRateDimension_FiniteRefinement_mean_deviation_le_coupling
import Theorems.Thm_OAI_EntropyRateDimension_FiniteRefinement_refinement_increment
import Theorems.Thm_OAI_EntropyRateDimension_ProductLaw_entropy
import Theorems.Thm_OAI_EntropyRateDimension_ProductLaw_observable_entropy
import Theorems.Thm_OAI_EntropyRateDimension_RandomGrid_cell_eq_distance_lt

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

theorem observableEntropy_fst_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ observableEntropy s p (fun a => (f a, g a)) := by
  exact observableEntropy_comp_le s p (fun a => (f a, g a)) Prod.fst hp

theorem conditionalEntropy_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    conditionalEntropy s p f g ≤ observableEntropy s p f := by
  dsimp only [conditionalEntropy]
  linarith [observableEntropy_pair_le s p f g hp hp1]

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

-- ---- from OAI.MeasureTheory.SelfSimilar.FairPairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

theorem cell_mass_pos {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x : ℝ} (hx : x ∈ ν.support) :
    0 < FiniteEntropy.mass ν.support ν.prob g (g x) := by
  apply lt_of_lt_of_le (ν.prob_pos x hx)
  apply Finset.single_le_sum
  · intro y hy
    exact (ν.prob_pos y (Finset.mem_filter.mp hy).1).le
  · exact Finset.mem_filter.mpr ⟨hx, rfl⟩

theorem conditionalCoupling_nonneg {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x y : ℝ} (hx : x ∈ ν.support) (hy : y ∈ ν.support) :
    0 ≤ conditionalCoupling ν g x y := by
  unfold conditionalCoupling
  split_ifs
  · exact div_nonneg (mul_nonneg (ν.prob_pos x hx).le (ν.prob_pos y hy).le)
      (cell_mass_pos ν g hx).le
  · exact le_rfl

theorem conditionalCoupling_symm {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) (x y : ℝ) :
    conditionalCoupling ν g x y = conditionalCoupling ν g y x := by
  by_cases h : g x = g y
  · simp only [conditionalCoupling, h, ite_true, mul_comm]
  · simp only [conditionalCoupling, h, Ne.symm h, ite_false]

theorem conditionalCoupling_row {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x : ℝ} (hx : x ∈ ν.support) :
    ∑ y ∈ ν.support, conditionalCoupling ν g x y = ν.prob x := by
  classical
  have hp := ne_of_gt (cell_mass_pos ν g hx)
  unfold conditionalCoupling
  simp only [eq_comm (a := g x), ← Finset.sum_filter]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change ν.prob x * FiniteEntropy.mass ν.support ν.prob g (g x) /
    FiniteEntropy.mass ν.support ν.prob g (g x) = _
  exact mul_div_cancel_right₀ _ hp

theorem conditionalCoupling_eq_zero_of_ne {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x y : ℝ} (h : g x ≠ g y) :
    conditionalCoupling ν g x y = 0 := by
  simp only [conditionalCoupling, h, ite_false]

end FairPairs

end EntropyRateDimension

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

theorem weight_sum (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    ∑ x, weight p x = 1 := by
  simpa only [weight, hp, Finset.prod_const_one] using (Fintype.prod_sum p).symm

variable {β : Type uβ} [DecidableEq β]

end ProductLaw

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.GridCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace RandomGrid

attribute [local instance] unitCircleProbability
theorem shift_zero : shift 0 = 0 := by
  have hh := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := (0 : ℝ))
    (y := (0 : ℝ)) (by norm_num : (0 : ℝ) ∈ Set.Ico 0 (0+1))
  simpa only [shift, AddCircle.coe_zero] using hh

end RandomGrid

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.SumsetBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uβ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FairPairs

open FiniteEntropy

theorem Law.support_nonempty (ν : Law) : ν.support.Nonempty := by
  by_contra h
  have := ν.prob_sum
  rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at this
  norm_num at this

theorem mass_support {β : Type uβ} [DecidableEq β] (ν : Law) (g : ℝ → β) (b : β) :
    mass Finset.univ (fun a : ν.support => ν.prob a) (fun a => g a) b =
      mass ν.support ν.prob g b := by
  classical
  simp only [mass, Finset.sum_filter]
  exact Finset.sum_coe_sort ν.support (fun a => if g a = b then ν.prob a else 0)

theorem sum_support₂ (ν : Law) (f : ℝ → ℝ → ℝ) :
    (∑ a : ν.support, ∑ b : ν.support, f a b) = ∑ a ∈ ν.support, ∑ b ∈ ν.support, f a b := by
  calc
    _ = ∑ a : ν.support, ∑ b ∈ ν.support, f a b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_coe_sort ν.support (f a)
    _ = _ := Finset.sum_coe_sort ν.support (fun a => ∑ b ∈ ν.support, f a b)

theorem mean_deviation_le_bandCost {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) (R : ℝ)
    (hd : ∀ a ∈ ν.support, ∀ b ∈ ν.support, g a = g b → |a-b| ≤ R) :
    (∑ a : ν.support, ν.prob a * |(a : ℝ)-FiniteRefinement.cellMean
      (fun b : ν.support => ν.prob b) (fun b => (b : ℝ)) (fun b => g b) (g a)|) ≤
      ν.bandCost R := by
  classical
  have hj := FiniteRefinement.mean_deviation_le_coupling
    (fun a : ν.support => ν.prob a) (fun a => (a : ℝ)) (fun a => g a)
    (fun a => ν.prob_pos a a.property)
  have he : (∑ a : ν.support, ∑ b : ν.support,
      (if g a = g b then ν.prob a*ν.prob b /
        mass Finset.univ (fun x : ν.support => ν.prob x) (fun x => g x) (g a) else 0)*
      |(a : ℝ)-(b : ℝ)|) =
      ∑ a ∈ ν.support, ∑ b ∈ ν.support, conditionalCoupling ν g a b * |b-a| := by
    simp only [mass_support, conditionalCoupling, abs_sub_comm]
    exact sum_support₂ ν (fun a b => (if g a = g b then ν.prob a*ν.prob b /
      mass ν.support ν.prob g (g a) else 0) * |a-b|)
  rw [he] at hj
  apply hj.trans
  exact coupling_distance_le (conditionalCoupling ν g) R
    (fun x hx y hy => conditionalCoupling_nonneg ν g hx hy)
    (fun x _ y _ => conditionalCoupling_symm ν g x y)
    (fun x hx => (conditionalCoupling_row ν g hx).le)
    (by
      intro x hx y hy hxy
      apply conditionalCoupling_eq_zero_of_ne
      intro he
      have hh := hd x hx y hy he
      rw [abs_sub_comm] at hh
      exact (not_le_of_gt hxy) hh)

theorem exists_capacity_refinement (ν : Law) (g : ℝ → List ℤ)
    (k : ℕ) (hk : 1 ≤ k) (R : ℝ) (hR : 0 < R)
    (hd : ∀ a ∈ ν.support, ∀ b ∈ ν.support, g a = g b → |a-b| ≤ R) :
    ∃ g' : ℝ → List ℤ,
      (∀ a ∈ ν.support, ∀ b ∈ ν.support, g' a = g' b → |a-b| ≤ R/4) ∧
      conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => fun a : ν.support => ν.prob a))
        (fun x i => g' (x i)) (fun x => ∑ i, (x i : ℝ)) ≤
      conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => fun a : ν.support => ν.prob a))
        (fun x i => g (x i)) (fun x => ∑ i, (x i : ℝ)) +
      (352*k^4/R)*ν.bandCost R*Real.log 2 := by
  classical
  let p : ν.support → ℝ := fun a => ν.prob a
  have hp : ∀ a, 0 < p a := fun a => ν.prob_pos a a.property
  obtain ⟨u,hu⟩ := FiniteRefinement.exists_entropy_step p (fun a => (a : ℝ)) (fun a => g a)
    hp ν.subtype_sum k hk (R/4) (by positivity) (by
      intro a b hab
      simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using hd a a.property b b.property hab)
  refine ⟨fun a => RandomGrid.cell (R/4) u a :: g a, ?_, ?_⟩
  · intro a _ b _ he
    exact (RandomGrid.cell_eq_distance_lt (by positivity) u (List.cons.inj he).1).le
  · rw [FiniteRefinement.refinement_increment p (fun a => (a : ℝ)) (fun a => g a)
      (fun a => (hp a).le) k (R/4) u]
    apply add_le_add le_rfl
    apply hu.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mean_deviation_le_bandCost ν g R hd)
        (by positivity : 0 ≤ (88 : ℝ)*k^4/(R/4)))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    convert hh using 1; ring

theorem exists_fine_partition (ν : Law) (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : 0 < ρ) (J : ℕ) :
    ∃ g : ℝ → List ℤ,
      (∀ a ∈ ν.support, ∀ b ∈ ν.support, g a = g b → |a-b| ≤ ρ/4^J) ∧
      ν.partitionEntropy k g ≤ ν.partitionEntropy k (fun x => [⌊x/ρ⌋]) +
        ∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h) := by
  classical
  induction J with
  | zero =>
    refine ⟨fun x => [⌊x/ρ⌋], ?_, ?_⟩
    · intro a _ b _ he
      have hh : RandomGrid.cell ρ 0 a = RandomGrid.cell ρ 0 b := by
        simpa only [RandomGrid.cell, RandomGrid.shift_zero, add_zero] using (List.cons.inj he).1
      simpa only [pow_zero, div_one] using (RandomGrid.cell_eq_distance_lt hρ 0 hh).le
    · simp only [Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ J ih =>
    obtain ⟨g,hd,hg⟩ := ih
    obtain ⟨g',hd',hg'⟩ := exists_capacity_refinement ν g k hk (ρ/4^J) (by positivity) hd
    refine ⟨g', ?_, ?_⟩
    · intro a ha b hb he
      simpa only [pow_succ, div_div] using hd' a ha b hb he
    · change ν.partitionEntropy k g' ≤ ν.partitionEntropy k g + ν.refinementCost k (ρ/4^J) at hg'
      rw [Finset.sum_range_succ]
      linarith

theorem exists_separating_depth (ν : Law) (ρ : ℝ) :
    ∃ J : ℕ, ∀ a ∈ ν.support, ∀ b ∈ ν.support, a ≠ b → ρ/4^J < |a-b| := by
  classical
  have ht : Filter.Tendsto (fun n : ℕ => ρ/(4 : ℝ)^n) Filter.atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1 : ℝ)/4 < 1)).const_mul ρ
    simpa only [div_pow, one_pow, mul_zero, div_eq_mul_inv, one_mul, inv_pow] using hh
  have he : ∀ᶠ J : ℕ in Filter.atTop,
      ∀ a ∈ ν.support, ∀ b ∈ ν.support, a ≠ b → ρ/4^J < |a-b| := by
    apply (Filter.eventually_all_finset ν.support).mpr
    intro a ha
    apply (Filter.eventually_all_finset ν.support).mpr
    intro b hb
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (fun _ h => (h hab).elim)
    · exact (ht.eventually (isOpen_Iio.mem_nhds (abs_pos.mpr (sub_ne_zero.mpr hab)))).mono
        (fun J h _ => h)
  exact he.exists

theorem observableEntropy_support {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) :
    observableEntropy Finset.univ (fun a : ν.support => ν.prob a) (fun a => g a) =
      observableEntropy ν.support ν.prob g := by
  classical
  have he : (Finset.univ : Finset ν.support).image (fun a : ν.support => g (a : ℝ)) = ν.support.image g := by
    ext b
    constructor
    · intro hb
      obtain ⟨a,_,hab⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨a,a.property,hab⟩
    · intro hb
      obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,hab⟩
  simp only [observableEntropy, he, entropy, mass_support]

theorem pair_bound_natural (ν : Law) (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) :
    k * (entropy ν.support ν.prob - observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋)) ≤
      Real.log (ν.sumset k).card + 60000*k^4*Real.log 2 *
        ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ), capacity ν ℓ := by
  classical
  obtain ⟨a,ha⟩ := ν.support_nonempty
  have : Nonempty ν.support := ⟨⟨a,ha⟩⟩
  let p : ν.support → ℝ := fun a => ν.prob a
  let w := ProductLaw.weight (fun _ : Fin k => p)
  let Y : (Fin k → ν.support) → ℝ := fun x => ∑ i, (x i : ℝ)
  let C₀ : (Fin k → ν.support) → Fin k → List ℤ := fun x i => [⌊(x i : ℝ)/ρ⌋]
  have hp : ∀ a, 0 ≤ p a := fun a => (ν.prob_pos a a.property).le
  have hw : ∀ x ∈ (Finset.univ : Finset (Fin k → ν.support)), 0 ≤ w x :=
    fun x _ => ProductLaw.weight_nonneg _ (fun _ a => hp a) x
  have hw1 : ∑ x, w x = 1 := ProductLaw.weight_sum _ (fun _ => ν.subtype_sum)
  obtain ⟨J,hJ⟩ := exists_separating_depth ν ρ
  obtain ⟨g,hd,hg⟩ := exists_fine_partition ν k hk ρ hρ J
  let G : (Fin k → ν.support) → Fin k → List ℤ := fun x i => g (x i)
  have hi : Function.Injective (fun a : ν.support => g a) := by
    intro a b he
    apply Subtype.ext
    by_contra hab
    exact (not_lt_of_ge (hd a a.property b b.property he)) (hJ a a.property b b.property hab)
  have hG : Function.Injective G := by
    intro x y he
    funext i
    exact hi (congrFun he i)
  have hent : observableEntropy Finset.univ w G = k*entropy ν.support ν.prob := by
    rw [observableEntropy_of_injective Finset.univ w G hw hG, ProductLaw.entropy _ (fun _ => ν.subtype_sum)]
    have he : entropy Finset.univ p = entropy ν.support ν.prob :=
      Finset.sum_coe_sort ν.support (fun a => Real.negMulLog (ν.prob a))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact congrArg (fun z => (k : ℝ)*z) he
  have hinit : observableEntropy Finset.univ w C₀ =
      k*observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋) := by
    rw [ProductLaw.observable_entropy p (fun a : ν.support => [⌊(a : ℝ)/ρ⌋]) hp ν.subtype_sum]
    simp only [Fintype.card_fin]
    rw [observableEntropy_support ν (fun a => [⌊a/ρ⌋])]
    congr 1
    apply observableEntropy_eq_of_fibers _ _ _ _ (fun x hx => (ν.prob_pos x hx).le)
    intro x _ y _
    simp only [List.cons.injEq, and_true]
  have hy : observableEntropy Finset.univ w Y ≤ Real.log (ν.sumset k).card :=
    observableEntropy_le_log_on_superset Finset.univ (ν.sumset k) w Y
      (fun x _ => Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩) hw hw1
  have hjoint := observableEntropy_fst_le Finset.univ w G Y hw
  have hcinit := conditionalEntropy_le Finset.univ w C₀ Y hw hw1
  have hsum := sum_refinementCost_le ν k ρ hρ J
  change conditionalEntropy Finset.univ w G Y ≤ conditionalEntropy Finset.univ w C₀ Y + _ at hg
  rw [hent] at hjoint
  rw [hinit] at hcinit
  unfold conditionalEntropy at hg hcinit
  linarith

end FairPairs

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.FairPairs.pair_bound_natural := @_root_.OAI.EntropyRateDimension.FairPairs.pair_bound_natural
