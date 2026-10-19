-- Prove2me | solution 1 for OAI.EntropyRateDimension.System.uniform_nonsaturation_of_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:14:25.823398+00:00
-- url     : https://prove2.me/submissions/c3672c2e-4b28-475a-b858-a4a1818b4fa6

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/EntropyBounds.lean:L172-L208
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.System.uniform_nonsaturation_of_entropy_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_mixture
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_js_le_tv
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_map_affine
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_fairShift
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_nested_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_scale
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_gridDeficit_eq_js
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_grid_le_grid_add_log
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_comp
import Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_compact

-- ---- from OAI.MeasureTheory.SelfSimilar.Basic ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem affine_continuous (S : System ι) (i : ι) : Continuous (S.affine i) := by
  unfold affine
  fun_prop

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end System

theorem binaryEntropy_quadratic_concave :
    ConcaveOn ℝ (Set.Icc 0 1) (fun x : ℝ => Real.binEntropy x+2*x^2) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun x =>
    Real.log (1-x)-Real.log x+4*x) (f'' := fun x => -(1-x)⁻¹-x⁻¹+4)
    (convex_Icc 0 1) (Real.binEntropy_continuous.add (by fun_prop)).continuousOn
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hd := (Real.hasDerivAt_binEntropy (ne_of_gt hx.1) (ne_of_lt hx.2)).add
      (((hasDerivAt_id x).pow 2).const_mul 2)
    exact (hd.congr_deriv (by dsimp; ring)).hasDerivWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hd := (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log (by linarith : 1-x ≠ 0)).sub
      ((hasDerivAt_id x).log (ne_of_gt hx.1))
    exact ((hd.add ((hasDerivAt_id x).const_mul 4)).congr_deriv (by dsimp; ring)).hasDerivWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hpos : 0 < x*(1-x) := mul_pos hx.1 (by linarith)
    have he : -(1-x)⁻¹-x⁻¹+4 = (4*x*(1-x)-1)/(x*(1-x)) := by
      field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
      ring
    rw [he]
    apply div_nonpos_of_nonpos_of_nonneg _ hpos.le
    nlinarith [sq_nonneg (2*x-1)]

theorem binaryEntropy_midpoint_gap (a b : ℝ) (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) :
    (a-b)^2/2 ≤ Real.binEntropy ((a+b)/2)-
      (Real.binEntropy a+Real.binEntropy b)/2 := by
  have hh := binaryEntropy_quadratic_concave.2 ha hb
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  simp only [smul_eq_mul] at hh
  have he : (1/2 : ℝ)*a+(1/2)*b=(a+b)/2 := by ring
  rw [he] at hh
  nlinarith [hh]

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

theorem observableEntropy_const_of {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (p : α → ℝ) (f : α → β) (b : β) (hf : ∀ a ∈ s, f a = b) :
    observableEntropy s p f = Real.negMulLog (∑ a ∈ s, p a) := by
  classical
  rw [observableEntropy_on_superset s {b} p f (fun a ha => Finset.mem_singleton.mpr (hf a ha))]
  simp only [entropy, Finset.sum_singleton, mass]
  rw [Finset.filter_eq_self.mpr hf]

theorem observableEntropy_bool {α : Type uα} (s : Finset α) (p : α → ℝ)
    (f : α → Bool) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p f = Real.binEntropy (mass s p f true) := by
  have hsum := sum_mass_mul s Finset.univ p f (fun _ => 1) (fun _ _ => Finset.mem_univ _)
  have hm : mass s p f false = 1 - mass s p f true := by
    simp only [mul_one, Fintype.sum_bool, hp1] at hsum
    linarith
  rw [observableEntropy_on_superset s Finset.univ p f (fun _ _ => Finset.mem_univ _)]
  simp only [entropy, Fintype.sum_bool, hm,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem mass_subset {α : Type uα} {β : Type uβ} [DecidableEq β] {s t : Finset α}
    (p : α → ℝ) (f : α → β) (hst : s ⊆ t)
    (hp : ∀ x ∈ t, x ∉ s → p x = 0) (b : β) : mass s p f b = mass t p f b := by
  classical
  apply Finset.sum_subset (Finset.filter_subset_filter _ hst)
  intro x hx hn
  exact hp x (Finset.mem_filter.mp hx).1 (fun hs => hn (Finset.mem_filter.mpr ⟨hs,(Finset.mem_filter.mp hx).2⟩))

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

theorem conditionalEntropy_midpoint {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (f : α → β) (g : α → γ) :
    (conditionalEntropy s p f g+conditionalEntropy s q f g)/2 ≤
      conditionalEntropy s (fun a => (p a+q a)/2) f g := by
  let P : Bool → α → ℝ := fun b => if b then p else q
  have hh := conditionalEntropy_mixture Finset.univ s (fun _ : Bool => (1/2 : ℝ))
    P f g (by intros; positivity) (by intro b _; cases b <;> assumption)
      (by intro b _; cases b <;> assumption)
  have he : (fun a => ∑ b : Bool, (1/2 : ℝ)*P b a) = fun a => (p a+q a)/2 := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [he] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte] at hh
  linarith

theorem js_observable_le {α : Type uα} {β : Type uβ} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (g : α → β) :
    observableEntropy s (fun a => (p a+q a)/2) g-
      (observableEntropy s p g+observableEntropy s q g)/2 ≤ js s p q := by
  have hh := conditionalEntropy_midpoint s p q hp hq hp1 hq1 id g
  rw [conditionalEntropy_id s p g hp, conditionalEntropy_id s q g hq,
    conditionalEntropy_id s _ g (fun a ha => div_nonneg (add_nonneg (hp a ha) (hq a ha)) (by norm_num))] at hh
  unfold js
  linarith

theorem js_nonneg {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) : 0 ≤ js s p q := by
  have hh := js_observable_le s p q hp hq hp1 hq1 (fun _ => ())
  have hm1 : (∑a∈s, (p a+q a)/2)=1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hp1, hq1]
    norm_num
  rw [observableEntropy_const_of s p (fun _ => ()) () (by intros; rfl),
    observableEntropy_const_of s q (fun _ => ()) () (by intros; rfl),
    observableEntropy_const_of s _ (fun _ => ()) () (by intros; rfl), hp1, hq1, hm1] at hh
  simpa only [Real.negMulLog_one, add_zero, zero_div, sub_zero] using hh

theorem event_sq_le_two_js {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (f : α → Bool) :
    (mass s p f true-mass s q f true)^2 ≤ 2*js s p q := by
  have hh := js_observable_le s p q hp hq hp1 hq1 f
  have hm1 : (∑a∈s, (p a+q a)/2)=1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hp1, hq1]
    norm_num
  rw [observableEntropy_bool s p f hp1, observableEntropy_bool s q f hq1,
    observableEntropy_bool s _ f hm1] at hh
  have hm : mass s (fun a => (p a+q a)/2) f true =
      (mass s p f true+mass s q f true)/2 := by
    simp only [mass, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hm] at hh
  have hple : mass s p f true ≤ 1 := by
    rw [mass, ← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun a ha _ => hp a ha)
  have hqle : mass s q f true ≤ 1 := by
    rw [mass, ← hq1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun a ha _ => hq a ha)
  have hg := binaryEntropy_midpoint_gap (mass s p f true) (mass s q f true)
    ⟨mass_nonneg s p f hp true,hple⟩ ⟨mass_nonneg s q f hq true,hqle⟩
  linarith

theorem totalVariation_eq_event {α : Type uα} (s : Finset α) (p q : α → ℝ)
    (hp1 : ∑ a ∈ s, p a=1) (hq1 : ∑ a ∈ s, q a=1) :
    totalVariation s p q = mass s p (fun a => decide (q a ≤ p a)) true-
      mass s q (fun a => decide (q a ≤ p a)) true := by
  classical
  have he (a : α) : |p a-q a|=2*(if q a ≤ p a then p a-q a else 0)-(p a-q a) := by
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt (lt_of_not_ge h)))]; ring
  simp_rw [totalVariation, he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hp1, hq1]
  simp only [sub_self, sub_zero, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [mass, Finset.sum_filter, decide_eq_true_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

theorem totalVariation_sq_le_two_js {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) :
    (totalVariation s p q)^2 ≤ 2*js s p q := by
  rw [totalVariation_eq_event s p q hp1 hq1]
  exact event_sq_le_two_js s p q hp hq hp1 hq1 _

theorem totalVariation_triangle {α : Type uα} (s : Finset α) (p q r : α → ℝ) :
    totalVariation s p r ≤ totalVariation s p q+totalVariation s q r := by
  unfold totalVariation
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => abs_sub_le _ _ _)) (by norm_num)

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteDistribution ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension

namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

theorem entropy_on {α : Type uα} (p : FiniteDistribution α) (s : Finset α)
    (hs : p.support ⊆ s) : p.entropy=FiniteEntropy.entropy s p.weight := by
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hs h)), Real.negMulLog_zero]

theorem tv_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.tv q=FiniteEntropy.totalVariation s p.weight q.weight := by
  unfold tv FiniteEntropy.totalVariation
  congr 1
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hp h)), q.vanish a (fun h => ha (hq h)), sub_self, abs_zero]

theorem js_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.js q=FiniteEntropy.js s p.weight q.weight := by
  classical
  rw [js, (p.mix q).entropy_on s (Finset.union_subset hp hq), p.entropy_on s hp, q.entropy_on s hq]
  rfl

theorem js_nonneg {α : Type uα} (p q : FiniteDistribution α) : 0 ≤ p.js q := by
  classical
  rw [p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.js_nonneg _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)

theorem tv_nonneg {α : Type uα} (p q : FiniteDistribution α) : 0 ≤ p.tv q :=
  div_nonneg (tsum_nonneg (fun a => abs_nonneg _)) (by norm_num)

theorem tv_sq_le_two_js {α : Type uα} (p q : FiniteDistribution α) : (p.tv q)^2 ≤ 2*p.js q := by
  classical
  rw [p.tv_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right,
    p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.totalVariation_sq_le_two_js _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)

theorem js_le_tv {α : Type uα} (p q : FiniteDistribution α) : p.js q ≤ p.tv q*Real.log 2 := by
  classical
  rw [p.tv_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right,
    p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.js_le_tv _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)

theorem tv_triangle {α : Type uα} (p q r : FiniteDistribution α) : p.tv r ≤ p.tv q+q.tv r := by
  classical
  let s := p.support ∪ q.support ∪ r.support
  have hp : p.support ⊆ s := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hr : r.support ⊆ s := Finset.subset_union_right
  rw [p.tv_on r s hp hr, p.tv_on q s hp hq, q.tv_on r s hq hr]
  exact FiniteEntropy.totalVariation_triangle _ _ _ _

theorem map_weight_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) (b : β) :
    (p.map f).weight b=FiniteEntropy.mass s p.weight f b := by
  classical
  exact FiniteEntropy.mass_subset p.weight f hs (fun a _ ha => p.vanish a ha) b

theorem entropy_map_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) :
    (p.map f).entropy=FiniteEntropy.observableEntropy s p.weight f := by
  classical
  rw [(p.map f).entropy_on (s.image f) (Finset.image_subset_image hs)]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (p.map_weight_on f s hs b))

theorem mix_map_entropy {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hp : p.support ⊆ s) (hq : q.support ⊆ s) :
    ((p.map f).mix (q.map f)).entropy=
      FiniteEntropy.observableEntropy s (fun a => (p.weight a+q.weight a)/2) f := by
  classical
  rw [((p.map f).mix (q.map f)).entropy_on (s.image f)
    (Finset.union_subset (Finset.image_subset_image hp) (Finset.image_subset_image hq))]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change ((p.map f).weight b+(q.map f).weight b)/2=_
  rw [p.map_weight_on f s hp, q.map_weight_on f s hq]
  simp only [FiniteEntropy.mass, ← Finset.sum_div, Finset.sum_add_distrib]

theorem js_map_le {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    (p.map f).js (q.map f) ≤ p.js q := by
  classical
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [js, mix_map_entropy p q f s hp hq, p.entropy_map_on f s hp,
    q.entropy_map_on f s hq, p.js_on q s hp hq]
  exact FiniteEntropy.js_observable_le s _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on s hp) (q.sum_on s hq) f

theorem entropy_congr {α : Type uα} (p q : FiniteDistribution α) (h : p.weight=q.weight) :
    p.entropy=q.entropy := by
  unfold entropy
  rw [h]

theorem tv_congr {α : Type uα} (p q p' q' : FiniteDistribution α)
    (hp : p.weight=p'.weight) (hq : q.weight=q'.weight) : p.tv q=p'.tv q' := by
  unfold tv
  rw [hp,hq]

theorem js_congr {α : Type uα} (p q p' q' : FiniteDistribution α)
    (hp : p.weight=p'.weight) (hq : q.weight=q'.weight) : p.js q=p'.js q' := by
  unfold js
  rw [p.entropy_congr p' hp,q.entropy_congr q' hq]
  congr 1
  apply entropy_congr
  funext a
  change (p.weight a+q.weight a)/2=(p'.weight a+q'.weight a)/2
  rw [hp,hq]

theorem map_weight_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} (p : FiniteDistribution α) (f : α → β) (g : β → γ) :
    ((p.map f).map g).weight=(p.map (g ∘ f)).weight := by
  funext c
  exact FiniteEntropy.mass_comp p.support p.weight f g c

theorem map_weight_of_injective {α : Type uα} {β : Type uβ} (p : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) (a : α) :
    (p.map f).weight (f a)=p.weight a := by
  change FiniteEntropy.mass p.support p.weight f (f a)=p.weight a
  simp only [FiniteEntropy.mass, Finset.sum_filter, hf.eq_iff]
  rw [Finset.sum_ite_eq']
  by_cases ha : a ∈ p.support
  · simp only [ha, ↓reduceIte]
  · simp only [ha, ↓reduceIte, p.vanish a ha]

theorem tv_map_injective {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) : (p.map f).tv (q.map f)=p.tv q := by
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [(p.map f).tv_on (q.map f) (s.image f)
    (Finset.image_subset_image hp) (Finset.image_subset_image hq), p.tv_on q s hp hq]
  unfold FiniteEntropy.totalVariation
  rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [p.map_weight_of_injective f hf, q.map_weight_of_injective f hf]

theorem translate_weight (p : FiniteDistribution ℤ) (j a : ℤ) :
    (p.translate j).weight a=p.weight (a-j) := by
  change (p.map (fun a => a+j)).weight a=p.weight (a-j)
  convert p.map_weight_of_injective (fun a => a+j) (add_left_injective j) (a-j) using 1; simp

theorem tv_translate (p q : FiniteDistribution ℤ) (j : ℤ) :
    (p.translate j).tv (q.translate j)=p.tv q :=
  p.tv_map_injective q _ (add_left_injective j)

theorem translate_add (p : FiniteDistribution ℤ) (i j : ℤ) :
    ((p.translate i).translate j).weight=(p.translate (i+j)).weight := by
  funext a
  rw [translate_weight,translate_weight,translate_weight]
  congr 1
  omega

theorem tv_translate_two (p : FiniteDistribution ℤ) :
    p.tv (p.translate 2) ≤ 2*p.tv (p.translate 1) := by
  have hh := tv_triangle p (p.translate 1) (p.translate 2)
  have he : (p.translate 1).tv (p.translate 2)=p.tv (p.translate 1) := by
    rw [← p.tv_translate (p.translate 1) 1]
    exact tv_congr _ _ _ _ rfl (p.translate_add 1 1).symm
  rw [he] at hh
  linarith

theorem js_two_step_coarsen (p : FiniteDistribution ℤ) (f : ℤ → ℤ) :
    ((p.map f).js ((p.translate 2).map f))^2 ≤
      8*(Real.log 2)^2*p.js (p.translate 1) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h0 := js_nonneg (p.map f) ((p.translate 2).map f)
  have h1 := (js_map_le p (p.translate 2) f).trans (js_le_tv p (p.translate 2))
  have h2 := mul_le_mul_of_nonneg_right (tv_translate_two p) hlog
  have h3 := tv_sq_le_two_js p (p.translate 1)
  have htv := tv_nonneg p (p.translate 1)
  have hh : ((p.map f).js ((p.translate 2).map f))^2 ≤
      (2*p.tv (p.translate 1)*Real.log 2)^2 := by
    exact sq_le_sq₀ h0 (by positivity) |>.mpr (h1.trans h2)
  nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg (Real.log 2))]

theorem tv_le_one {α : Type uα} (p q : FiniteDistribution α) : p.tv q ≤ 1 := by
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [p.tv_on q s hp hq]
  unfold FiniteEntropy.totalVariation
  have hh : (∑ a ∈ s, |p.weight a-q.weight a|) ≤ 2 := by
    calc
      _ ≤ ∑ a ∈ s, (p.weight a+q.weight a) := by
        apply Finset.sum_le_sum
        intro a _
        exact abs_sub_le_iff.mpr ⟨by linarith [q.nonneg a], by linarith [p.nonneg a]⟩
      _ = 2 := by rw [Finset.sum_add_distrib, p.sum_on s hp, q.sum_on s hq]; norm_num
  linarith

theorem js_le_log_two {α : Type uα} (p q : FiniteDistribution α) : p.js q ≤ Real.log 2 := by
  calc
    _ ≤ p.tv q*Real.log 2 := js_le_tv p q
    _ ≤ 1*Real.log 2 := mul_le_mul_of_nonneg_right (tv_le_one p q) (Real.log_nonneg (by norm_num))
    _ = _ := one_mul _

theorem map_translate_div_two (p : FiniteDistribution ℤ) :
    ((p.translate 2).map (fun n => n/2)).weight=
      ((p.map (fun n => n/2)).translate 1).weight := by
  change ((p.map (fun n => n+2)).map (fun n => n/2)).weight=
    ((p.map (fun n => n/2)).map (fun n => n+1)).weight
  rw [map_weight_comp, map_weight_comp]
  congr 2
  funext n
  dsimp only [Function.comp_apply]
  omega

end FiniteDistribution

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

theorem grid_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    IntervalIntegrable (grid μ s) volume a b := by
  apply (grid_periodic μ hμ hs).intervalIntegrable₀ one_ne_zero
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr (grid_integrable μ hμ hs)

theorem averaged_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (b : ℝ) :
    averaged (μ.map (fun x => x+b)) s = averaged μ s := by
  simp only [averaged_eq_intervalIntegral, grid_translate]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ)] using
    (grid_periodic μ hμ hs).intervalIntegral_add_eq (b/s) 0

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

theorem averaged_affine (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s a : ℝ} (hs : 0 < s) (ha : a ≠ 0) (b : ℝ) :
    averaged (μ.map (fun x => a*x+b)) s = averaged μ (s/|a|) := by
  have hp : IsProbabilityMeasure (μ.map (fun x => a*x)) := (Measure.isProbabilityMeasure_map_iff (measurable_const.mul measurable_id).aemeasurable).2 inferInstance
  let := hp
  have hc : CompactlyCarried (μ.map (fun x => a*x)) := by
    simpa only [add_zero] using hμ.map_affine a 0
  have he : μ.map (fun x => a*x+b) = (μ.map (fun x => a*x)).map (fun x => x+b) := by
    rw [Measure.map_map (g := fun x : ℝ => x+b) (f := fun x : ℝ => a*x) (by fun_prop) (by fun_prop)]
    rfl
  rw [he, averaged_translate _ hc hs b, averaged_scale μ hμ hs ha]

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

theorem grid_le_grid_add_log_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log (t/s+2) := by
  have hc : (0 : ℝ) < (⌈t/s⌉ : ℝ)+1 := by
    have hh := Int.le_ceil (t/s)
    linarith [div_pos ht hs]
  have hu : (⌈t/s⌉ : ℝ)+1 ≤ t/s+2 := by linarith [Int.ceil_lt_add_one (t/s)]
  exact (grid_le_grid_add_log μ hμ hs ht u v).trans
    (add_le_add_right (Real.log_le_log hc hu) _)

theorem averaged_le_averaged_add_log_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t ≤ s) :
    averaged μ s ≤ averaged μ t + Real.log 2 := by
  have hi := (grid_integrable μ hμ ht).add (integrable_const (Real.log 2))
  have hh := integral_mono_ae (grid_integrable μ hμ hs) hi
    (Filter.Eventually.of_forall (fun u => grid_le_grid_add_log_two μ hμ hs ht hts u u))
  simp only [Pi.add_apply] at hh
  rw [integral_add (grid_integrable μ hμ ht) (integrable_const _)] at hh
  simpa [averaged, integral_const, Measure.real_def] using hh

theorem averaged_le_averaged_add_log_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    averaged μ s ≤ averaged μ t + Real.log (t/s+2) := by
  have hi := (grid_integrable μ hμ ht).add (integrable_const (Real.log (t/s+2)))
  have hh := integral_mono_ae (grid_integrable μ hμ hs) hi
    (Filter.Eventually.of_forall (fun u => grid_le_grid_add_log_ratio μ hμ hs ht u u))
  simp only [Pi.add_apply] at hh
  rw [integral_add (grid_integrable μ hμ ht) (integrable_const _)] at hh
  simpa [averaged, integral_const, Measure.real_def] using hh

theorem fairShift_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    IsProbabilityMeasure (fairShift μ v) := by
  let ν := fun i : Fin 2 => μ.map (fun x => x+(i : ℝ)*v)
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const _).aemeasurable).2 inferInstance
  let := this
  exact mixture_probability ν (fun _ => 1/2) (by intro; positivity) (by norm_num [Fin.sum_univ_two])

theorem CompactlyCarried.fairShift {μ : Measure ℝ} (hμ : CompactlyCarried μ) (v : ℝ) :
    CompactlyCarried (fairShift μ v) := by
  apply CompactlyCarried.mixture
  intro i
  simpa only [one_mul] using hμ.map_affine 1 ((i : ℝ)*v)

theorem gridDeficit_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    0 ≤ gridDeficit μ s u ∧ gridDeficit μ s u ≤ Real.log 2 := by
  rw [gridDeficit_eq_js μ hμ hs u]
  exact ⟨FiniteDistribution.js_nonneg _ _,FiniteDistribution.js_le_log_two _ _⟩

theorem gridLaw_coarsen_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    ((gridLaw μ hμ hs (2*u)).map (fun n : ℤ => n/2)).weight=
      (gridLaw μ hμ (mul_pos (by norm_num : (0 : ℝ)<2) hs) u).weight := by
  classical
  let : DecidableEq ℤ := fun _ _ => Classical.propDecidable _
  funext b
  rw [FiniteDistribution.map_weight_on _ _ _ (Finset.Subset.refl _)]
  change FiniteEntropy.mass (Finset.Icc ⌊-hμ.choose/s+2*u⌋ ⌊hμ.choose/s+2*u⌋) (mass μ (label s (2*u))) (fun n : ℤ => n/2) b=
    mass μ (label (2*s) u) b
  rw [← mass_comp μ (label s (2*u)) (label_measurable _ _) _
    (label_ae_finite μ hs hμ.choose_spec.2)]
  congr 1
  funext x
  symm
  simpa using label_nested s u x (by norm_num : 0 < (2 : ℕ))

theorem gridDeficit_double_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    (gridDeficit μ (2*s) u)^2 ≤ 8*(Real.log 2)^2*gridDeficit μ s (2*u) := by
  let p := gridLaw μ hμ hs (2*u)
  let q := gridLaw μ hμ (mul_pos (by norm_num : (0 : ℝ)<2) hs) u
  have he : (p.map (fun n => n/2)).weight=q.weight := gridLaw_coarsen_two μ hμ hs u
  have he' : ((p.translate 2).map (fun n => n/2)).weight=(q.translate 1).weight := by
    rw [FiniteDistribution.map_translate_div_two]
    funext b
    rw [FiniteDistribution.translate_weight, FiniteDistribution.translate_weight, he]
  have hh := FiniteDistribution.js_two_step_coarsen p (fun n => n/2)
  rw [FiniteDistribution.js_congr _ _ q (q.translate 1) he he'] at hh
  rw [gridDeficit_eq_js μ hμ (mul_pos (by norm_num : (0 : ℝ)<2) hs) u,
    gridDeficit_eq_js μ hμ hs (2*u)]
  exact hh

theorem gridDeficit_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    Integrable (gridDeficit μ s) (volume.restrict (Set.Icc 0 1)) := by
  let := fairShift_probability μ s
  exact (grid_integrable (fairShift μ s) (hμ.fairShift s) hs).sub (grid_integrable μ hμ hs)

theorem integral_gridDeficit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Icc (0 : ℝ) 1, gridDeficit μ s u)=
      Real.log 2-(averaged μ s-averaged μ (2*s)) := by
  let := fairShift_probability μ s
  simp only [gridDeficit]
  rw [integral_sub (grid_integrable _ (hμ.fairShift s) hs) (grid_integrable μ hμ hs)]
  change averaged (fairShift μ s) s-averaged μ s=_
  rw [averaged_fairShift μ hμ hs]
  ring

theorem deficit_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    0 ≤ deficit μ s ∧ deficit μ s ≤ Real.log 2 := by
  rw [deficit, ← integral_gridDeficit μ hμ hs]
  constructor
  · exact integral_nonneg (fun u => (gridDeficit_bounds μ hμ hs u).1)
  · have hh := integral_mono (gridDeficit_integrable μ hμ hs)
      (integrable_const (Real.log 2)) (fun u => (gridDeficit_bounds μ hμ hs u).2)
    simpa using hh

theorem gridDeficit_sq_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u => (gridDeficit μ s u)^2) (volume.restrict (Set.Icc 0 1)) := by
  apply (integrable_const ((Real.log 2)^2)).mono'
    ((gridDeficit_integrable μ hμ hs).aestronglyMeasurable.pow 2)
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  obtain ⟨h0,h1⟩ := gridDeficit_bounds μ hμ hs u
  exact pow_le_pow_left₀ h0 h1 2

theorem integral_gridDeficit_double_shift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Icc (0 : ℝ) 1, gridDeficit μ s (2*u))=deficit μ s := by
  let := fairShift_probability μ s
  have hi (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CompactlyCarried ν) :
      IntervalIntegrable (fun u => grid ν s (2*u)) volume 0 1 := by
    have h := (grid_intervalIntegrable ν hν hs 0 2).comp_mul_left (c := (2 : ℝ))
    norm_num at h
    exact h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  simp only [gridDeficit]
  have he (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CompactlyCarried ν) :
      (∫ u in (0 : ℝ)..1, grid ν s (2*u)) = averaged ν s := by
    simpa using averaged_grid_nsmul ν hν hs (by norm_num : 0 < (2 : ℕ))
  rw [intervalIntegral.integral_sub (hi _ (hμ.fairShift s)) (hi μ hμ),
    he _ (hμ.fairShift s), he μ hμ,
    averaged_fairShift μ hμ hs, deficit]
  ring

theorem deficit_double_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (deficit μ (2*s))^2 ≤ 8*(Real.log 2)^2*deficit μ s := by
  let := fairShift_probability μ s
  have ht : 0 < 2*s := mul_pos (by norm_num) hs
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have hj := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    (continuous_pow 2).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun u => (gridDeficit_bounds μ hμ ht u).1))
    (gridDeficit_integrable μ hμ ht) (gridDeficit_sq_integrable μ hμ ht)
  rw [integral_gridDeficit μ hμ ht] at hj
  change (deficit μ (2*s))^2 ≤ _ at hj
  have hi : Integrable (fun u => gridDeficit μ s (2*u))
      (volume.restrict (Set.Icc 0 1)) := by
    apply (integrable_const (Real.log 2)).mono'
      (((measurable_grid (fairShift μ s) s).sub (measurable_grid μ s)).comp
        (measurable_const.mul measurable_id)).aestronglyMeasurable
    filter_upwards [] with u
    exact (abs_of_nonneg (gridDeficit_bounds μ hμ hs (2*u)).1).le.trans
      (gridDeficit_bounds μ hμ hs (2*u)).2
  have hh := integral_mono (gridDeficit_sq_integrable μ hμ ht)
    (hi.const_mul (8*(Real.log 2)^2)) (gridDeficit_double_sq μ hμ hs)
  change (∫ u in Set.Icc (0 : ℝ) 1, (gridDeficit μ (2*s) u)^2) ≤ _ at hh
  rw [integral_const_mul, integral_gridDeficit_double_shift μ hμ hs] at hh
  exact hj.trans hh

theorem deficit_dyadic_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℕ → ℝ) (hv : ∀ n, 0 < v n)
    (h : Filter.Tendsto (fun n => deficit μ (v n)) Filter.atTop (nhds 0)) (j : ℕ) :
    Filter.Tendsto (fun n => deficit μ ((2 : ℝ)^j*v n)) Filter.atTop (nhds 0) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have hz : Filter.Tendsto (fun n => Real.sqrt (8*(Real.log 2)^2 *
        deficit μ ((2 : ℝ)^j*v n))) Filter.atTop (nhds 0) := by
      simpa using (ih.const_mul (8*(Real.log 2)^2)).sqrt
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    · intro n
      exact (deficit_bounds μ hμ (s := (2 : ℝ)^(j+1)*v n)
        (mul_pos (pow_pos (by norm_num) _) (hv n))).1
    · intro n
      apply Real.le_sqrt_of_sq_le
      have hb := deficit_double_sq μ hμ (s := (2 : ℝ)^j*v n)
        (mul_pos (pow_pos (by norm_num) _) (hv n))
      have he : (2 : ℝ)^(j+1)*v n = 2*((2 : ℝ)^j*v n) := by rw [pow_succ]; ring
      rwa [← he] at hb

theorem sum_dyadic_deficit (μ : Measure ℝ) (s : ℝ) (K : ℕ) :
    (∑j ∈ Finset.range K, deficit μ ((2 : ℝ)^j*s))=
      K*Real.log 2-(averaged μ s-averaged μ ((2 : ℝ)^K*s)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [deficit, Nat.cast_add, Nat.cast_one, pow_succ]
    have he : 2*((2 : ℝ)^K*s)=2^K*2*s := by ring
    rw [he]
    ring

theorem wide_window_saturation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℕ → ℝ) (hv : ∀ n, 0 < v n)
    (h : Filter.Tendsto (fun n => deficit μ (v n)) Filter.atTop (nhds 0)) (K : ℕ) :
    Filter.Tendsto (fun n => averaged μ (v n)-averaged μ ((2 : ℝ)^K*v n))
      Filter.atTop (nhds (K*Real.log 2)) := by
  have hh := tendsto_finsetSum (Finset.range K) (fun j _ => deficit_dyadic_tendsto_zero μ hμ v hv h j)
  simp only [sum_dyadic_deficit, Finset.sum_const_zero] at hh
  have ht := (tendsto_const_nhds (x := (K : ℝ)*Real.log 2)).sub hh
  simpa only [sub_sub_cancel, sub_zero] using ht

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.EntropyBounds ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
open MeasureEntropy

theorem stopped_lower (S : System ι) (F : ℝ → ℝ) {a v B : ℝ}
    (ha : 0 < a) (hai : ∀ i, a ≤ |S.ratio i|) (hv : 0 < v)
    (hstep : ∀ s, 0 < s → (∑ i, S.weight i*F (s/|S.ratio i|)) ≤ F s)
    (hbase : ∀ z, v ≤ z → z ≤ v/a → B ≤ F z) :
    ∀ s, 0 < s → s < v → B ≤ F s := by
  classical
  obtain ⟨c,_T,hc,hc1,_hT,hr,_ht⟩ := S.exists_uniform_bounds
  have hi : ∀ n s, 0 < s → v*c^n ≤ s → s ≤ v/a → B ≤ F s := by
    intro n
    induction n with
    | zero =>
      intro s _hs hvs hsa
      exact hbase s (by simpa using hvs) hsa
    | succ n ih =>
      intro s hs hvs hsa
      by_cases hvz : v ≤ s
      · exact hbase s hvz hsa
      have hsv : s < v := lt_of_not_ge hvz
      apply le_trans _ (hstep s hs)
      calc
        B = ∑i, S.weight i*B := by rw [← Finset.sum_mul, S.weight_sum, one_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (S.weight_nonneg i)
          apply ih _ (div_pos hs (S.ratio_pos i))
          · apply (le_div_iff₀ (S.ratio_pos i)).mpr
            calc
              v*c^n*|S.ratio i| ≤ v*c^n*c :=
                mul_le_mul_of_nonneg_left (hr i) (by positivity)
              _ ≤ s := by simpa only [pow_succ, mul_assoc] using hvs
          · exact (div_le_div_of_nonneg_left hv.le ha (hai i)).trans'
              (div_le_div_of_nonneg_right hsv.le (S.ratio_pos i).le)
  intro s hs hsv
  have hz : Filter.Tendsto (fun n : ℕ => v*c^n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1).const_mul v
  obtain ⟨n,hn⟩ := (hz.eventually (gt_mem_nhds hs)).exists
  have ha1 : a ≤ 1 := (hai (Classical.arbitrary ι)).trans
    (S.ratio_lt_one (Classical.arbitrary ι)).le
  exact hi n s hs hn.le (hsv.le.trans ((le_div_iff₀ ha).mpr (by nlinarith)))

theorem window_selfSimilar (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {s : ℝ} (hs : 0 < s) {K : ℕ} (hK : 0 < K) :
    (∑i, S.weight i*(averaged μ (s/|S.ratio i|)-
      averaged μ ((K : ℝ)*(s/|S.ratio i|)))) ≤
      averaged μ s-averaged μ ((K : ℝ)*s) := by
  classical
  obtain ⟨B,hB,hBμ⟩ := S.selfSimilar_compact μ hμ
  have hc : CompactlyCarried μ := ⟨B,hB.le,hBμ⟩
  let : ∀ i, IsProbabilityMeasure (μ.map (S.affine i)) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (S.affine_continuous i).measurable.aemeasurable).2 inferInstance
  have hh := averaged_nested_mixture μ hc (fun i => μ.map (S.affine i))
    (fun i => hc.map_affine (S.ratio i) (S.offset i)) S.weight S.weight_nonneg hμ hs hK
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  change _ = S.weight i*(averaged (μ.map (fun x => S.ratio i*x+S.offset i)) s-
    averaged (μ.map (fun x => S.ratio i*x+S.offset i)) ((K : ℝ)*s))
  rw [averaged_affine μ hc hs (abs_pos.mp (S.ratio_pos i)),
    averaged_affine μ hc (mul_pos (by exact_mod_cast hK) hs) (abs_pos.mp (S.ratio_pos i))]
  congr 2
  ring_nf

theorem stopped_window_transfer (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {a v : ℝ} (ha : 0 < a)
    (hai : ∀ i, a ≤ |S.ratio i|) (hv : 0 < v) {K : ℕ} (hK : 0 < K)
    {s : ℝ} (hs : 0 < s) (hsv : s < v) :
    averaged μ v-averaged μ ((K : ℝ)*v)-(Real.log (1/a+2)+Real.log 2) ≤
      averaged μ s-averaged μ ((K : ℝ)*s) := by
  obtain ⟨B,hB,hBμ⟩ := S.selfSimilar_compact μ hμ
  have hc : CompactlyCarried μ := ⟨B,hB.le,hBμ⟩
  apply S.stopped_lower (fun z => averaged μ z-averaged μ ((K : ℝ)*z)) ha hai hv
    (fun z hz => S.window_selfSimilar μ hμ hz hK) _ s hs hsv
  intro z hvz hza
  have hz : 0 < z := hv.trans_le hvz
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 := averaged_le_averaged_add_log_ratio μ hc hv hz
  have h2 := averaged_le_averaged_add_log_two μ hc (mul_pos hk hz) (mul_pos hk hv)
    (mul_le_mul_of_nonneg_left hvz hk.le)
  have hlog : Real.log (z/v+2) ≤ Real.log (1/a+2) := by
    apply Real.log_le_log (by positivity)
    suffices z/v ≤ 1/a by linarith
    apply (div_le_iff₀ hv).mpr
    simpa [div_eq_mul_inv, mul_comm] using hza
  linarith

end System

namespace MeasureEntropy

theorem geometric_gain_lower (F : ℝ → ℝ) {v K B : ℝ} (hv : 0 < v) (hK : 1 < K)
    (hg : ∀ s, 0 < s → s < v → B ≤ F s-F (K*s)) (m : ℕ) :
    F v+(m : ℝ)*B ≤ F (v*(1/K)^m) := by
  have hk : 0 < K := zero_lt_one.trans hK
  have hr : 0 < 1/K := div_pos zero_lt_one hk
  have hr1 : 1/K < 1 := (div_lt_one hk).mpr hK
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : 0 < v*(1/K)^(m+1) := mul_pos hv (pow_pos hr _)
    have hsv : v*(1/K)^(m+1) < v := by
      nlinarith [pow_lt_one₀ hr.le hr1 (by omega : m+1 ≠ 0)]
    have he : K*(v*(1/K)^(m+1))=v*(1/K)^m := by
      rw [pow_succ]
      field_simp
    have hh := hg _ hs hsv
    rw [he] at hh
    push_cast
    nlinarith

theorem geometric_gain_bound (F : ℝ → ℝ) {v K B d C : ℝ} (hv : 0 < v) (hK : 1 < K)
    (hu : ∀ s, 0 < s → s < 1 → F s ≤ d*Real.log (1/s)+C)
    (hg : ∀ s, 0 < s → s < v → B ≤ F s-F (K*s)) : B ≤ d*Real.log K := by
  have hk : 0 < K := zero_lt_one.trans hK
  have hr : 0 < 1/K := div_pos zero_lt_one hk
  have hr1 : 1/K < 1 := (div_lt_one hk).mpr hK
  have ht : Filter.Tendsto (fun n : ℕ => v*(1/K)^(n+1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).comp (Filter.tendsto_add_atTop_nat 1)
    simpa using h.const_mul v
  have he : ∀ᶠ n : ℕ in Filter.atTop,
      F v/((n : ℝ)+1)+B ≤ d*Real.log K + (C-d*Real.log v)/((n : ℝ)+1) := by
    filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with n hn
    have hg' := geometric_gain_lower F hv hK hg (n+1)
    have hu' := hu _ (mul_pos hv (pow_pos hr _)) hn
    have hlog : Real.log (1/(v*(1/K)^(n+1)))= ((n : ℝ)+1)*Real.log K-Real.log v := by
      rw [Real.log_div (by norm_num) (ne_of_gt (mul_pos hv (pow_pos hr _))), Real.log_one,
        Real.log_mul hv.ne' (pow_pos hr _).ne', Real.log_pow, Real.log_div (by norm_num) hk.ne',
        Real.log_one]
      push_cast
      ring
    rw [hlog] at hu'
    have hh : F v+((n : ℝ)+1)*B ≤ d*(((n : ℝ)+1)*Real.log K-Real.log v)+C := by
      exact_mod_cast hg'.trans hu'
    have hnpos : 0 < (n : ℝ)+1 := by positivity
    have hh' := (div_le_div_iff_of_pos_right hnpos).mpr hh
    have hl' : (F v+((n : ℝ)+1)*B)/((n : ℝ)+1) = F v/((n : ℝ)+1)+B := by
      field_simp
    have hr' : (d*(((n : ℝ)+1)*Real.log K-Real.log v)+C)/((n : ℝ)+1) =
        d*Real.log K+(C-d*Real.log v)/((n : ℝ)+1) := by
      field_simp
      ring
    rwa [hl',hr'] at hh'
  have hz : Filter.Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Filter.Tendsto (fun n : ℕ => F v/((n : ℝ)+1)+B) Filter.atTop (nhds B) := by
    simpa only [mul_one_div, mul_zero, zero_add] using (hz.const_mul (F v)).add_const B
  have hu' : Filter.Tendsto (fun n : ℕ => d*Real.log K+(C-d*Real.log v)/((n : ℝ)+1))
      Filter.atTop (nhds (d*Real.log K)) := by
    simpa only [mul_one_div, mul_zero, add_zero] using (hz.const_mul (C-d*Real.log v)).const_add (d*Real.log K)
  exact le_of_tendsto_of_tendsto hl hu' he

end MeasureEntropy

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
open MeasureEntropy

theorem uniform_nonsaturation_of_entropy_bound (S : System ι) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ) {d C : ℝ} (hd : d < 1)
    (hu : ∀ s, 0 < s → s < 1 → averaged μ s ≤ d*Real.log (1/s)+C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, 0 < v → δ ≤ deficit μ v := by
  classical
  obtain ⟨B,hB,hBμ⟩ := S.selfSimilar_compact μ hμ
  have hc : CompactlyCarried μ := ⟨B,hB.le,hBμ⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ (fun i => |S.ratio i|) Finset.univ_nonempty
  let a := |S.ratio i|
  have ha : 0 < a := S.ratio_pos i
  have hai : ∀ i, a ≤ |S.ratio i| := fun i => hi i (Finset.mem_univ i)
  let L := Real.log (1/a+2)+Real.log 2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨j,hj⟩ := exists_nat_gt (max 1 ((L+1)/((1-d)*Real.log 2)))
  have hjpos : 0 < j := by have := (le_max_left _ _).trans_lt hj; exact_mod_cast (lt_trans zero_lt_one this)
  have hgap : L+1 < (1-d)*(j*Real.log 2) := by
    have hh := (div_lt_iff₀ (mul_pos (sub_pos.mpr hd) hl)).mp ((le_max_right _ _).trans_lt hj)
    nlinarith
  by_contra! h
  choose v hv hvd using fun n : ℕ => h (1/((n : ℝ)+1)) (by positivity)
  have hzero : Filter.Tendsto (fun n => deficit μ (v n)) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => (deficit_bounds μ hc (hv n)).1) (fun n => (hvd n).le)
  have hw := wide_window_saturation μ hc v hv hzero j
  obtain ⟨n,hn⟩ := (hw.eventually (lt_mem_nhds (by linarith :
    (j : ℝ)*Real.log 2-1 < j*Real.log 2))).exists
  have hk : 1 < (2 : ℝ)^j := one_lt_pow₀ (by norm_num) (by omega)
  have ht : ∀ s, 0 < s → s < v n →
      averaged μ (v n)-averaged μ ((2 : ℝ)^j*v n)-L ≤
        averaged μ s-averaged μ ((2 : ℝ)^j*s) := by
    intro s hs hsn
    simpa only [L, Nat.cast_pow, Nat.cast_ofNat] using
      S.stopped_window_transfer μ hμ ha hai (hv n) (K := 2^j) (by positivity) hs hsn
  have hh := geometric_gain_bound (averaged μ) (hv n) hk hu ht
  rw [Real.log_pow] at hh
  nlinarith

end System

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureEntropy


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.System.uniform_nonsaturation_of_entropy_bound.{uι} := @_root_.OAI.EntropyRateDimension.System.uniform_nonsaturation_of_entropy_bound.{uι}
