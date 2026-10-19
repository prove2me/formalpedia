-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteRefinement.exists_entropy_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:50:13.912997+00:00
-- url     : https://prove2.me/submissions/be87e2fa-9438-41b3-b91a-6192c0ed3ef4

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteRefinement.lean:L222-L241
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteRefinement.exists_entropy_step. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_eq_sum
import Theorems.Thm_OAI_EntropyRateDimension_ProductLaw_moment
import Theorems.Thm_OAI_EntropyRateDimension_RandomGrid_exists_shift_variation_bound
import Theorems.Thm_OAI_EntropyRateDimension_RandomGrid_refinement_entropy_hit_bound

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

theorem conditionalEntropy_chain {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p (fun a => (f a, g a)) h =
      conditionalEntropy s p g h + conditionalEntropy s p f (fun a => (g a, h a)) := by
  have he := observableEntropy_equiv s p (fun a => ((f a, g a), h a))
    (Equiv.prodAssoc β γ δ) hp
  change observableEntropy s p (fun a => (f a, (g a, h a))) =
    observableEntropy s p (fun a => ((f a, g a), h a)) at he
  dsimp only [conditionalEntropy]
  linarith

theorem conditionalEntropy_disintegrate {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    conditionalEntropy s p f (fun x => (h x,g x)) =
      ∑ c ∈ s.image g, mass s p g c * conditionalEntropy
        (s.filter (fun x => g x = c)) (fun x => p x / mass s p g c) f h := by
  have hc := conditionalEntropy_chain s p f h g hp
  rw [conditionalEntropy_eq_sum s p (fun x => (f x,h x)) g hp,
      conditionalEntropy_eq_sum s p h g hp] at hc
  simp only [conditionalEntropy, mul_sub, Finset.sum_sub_distrib]
  dsimp only [conditionalEntropy] at hc
  linarith

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

theorem coordinate_event (p : ι → α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ i, ∑ a, p i a = 1) (i : ι) :
    (∑ x, if E i (x i) then weight p x else 0) = ∑ a, if E i a then p i a else 0 := by
  classical
  simpa only [Finset.prod_singleton, mul_ite, mul_one, mul_zero] using
    moment p (fun j a => if E j a then 1 else 0) {i} hp

theorem two_coordinate_events (p : ι → α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ i, ∑ a, p i a = 1)
    (i j : ι) (hij : i ≠ j) :
    (∑ x, if E i (x i) ∧ E j (x j) then weight p x else 0) =
      (∑ x, if E i (x i) then weight p x else 0) *
      (∑ x, if E j (x j) then weight p x else 0) := by
  classical
  rw [coordinate_event p E hp i, coordinate_event p E hp j]
  have h := moment p (fun l a => if E l a then 1 else 0) {i,j} hp
  simp only [Finset.prod_pair hij] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all
  · simp only [mul_ite, mul_one, mul_zero]

variable {β : Type uβ} [DecidableEq β]

theorem mass_cells (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) :
    FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c =
      ∏ i, cellMass p g c i := by
  classical
  have hh := (Fintype.prod_sum (fun i a => if g i a = c i then p i a else 0)).symm
  simpa only [Fintype.prod_ite_zero, ← funext_iff, FiniteEntropy.mass,
    Finset.sum_filter, weight, cellMass] using hh

theorem weight_conditional (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (x : ι → α) :
    weight (conditional p g c) x =
      if (fun i => g i (x i)) = c then weight p x /
        FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c else 0 := by
  classical
  rw [mass_cells]
  simp only [weight, conditional, Finset.prod_div_distrib, Fintype.prod_ite_zero, ← funext_iff]
  split_ifs <;> simp_all

theorem conditional_sum (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β)
    (hc : FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c ≠ 0) (i : ι) :
    ∑ a, conditional p g c i a = 1 := by
  rw [mass_cells] at hc
  have hi : cellMass p g c i ≠ 0 := (Finset.prod_ne_zero_iff.mp hc) i (Finset.mem_univ i)
  simp only [conditional, ← Finset.sum_div]
  exact div_self hi

omit [Fintype ι] [DecidableEq ι] in
theorem conditional_nonneg (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β)
    (hp : ∀ i a, 0 ≤ p i a) (i : ι) (a : α) : 0 ≤ conditional p g c i a := by
  have hn : ∀ j b, 0 ≤ (if g j b = c j then p j b else 0) := by
    intro j b
    split_ifs <;> first | exact hp j b | exact le_rfl
  exact div_nonneg (hn i a) (Finset.sum_nonneg (fun b _ => hn i b))

theorem conditional_event (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β)
    (E : (ι → α) → Prop) [DecidablePred E] :
    (∑ x ∈ Finset.univ.filter (fun x => (fun i => g i (x i)) = c),
      if E x then weight p x / FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c else 0) =
    ∑ x, if E x then weight (conditional p g c) x else 0 := by
  classical
  simp only [Finset.sum_filter, weight_conditional]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

end ProductLaw

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteRefinement ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteRefinement

open FiniteEntropy

variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem distance_mean_le (p : α → ℝ) (v : α → ℝ) (z R : ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hR : ∀ a, p a ≠ 0 → |z-v a| ≤ R) : |z - ∑ a, p a * v a| ≤ R := by
  have he : z - ∑ a, p a * v a = ∑ a, p a * (z-v a) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ a, |p a * (z-v a)|) ≤ ∑ a, p a * R := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg (hp a)]
      by_cases ha : p a = 0
      · simp only [ha, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hR a ha) (hp a)
    _ = R := by rw [← Finset.sum_mul, hp1, one_mul]

omit [Fintype α] in
theorem mass_pos {γ : Type uγ} [DecidableEq γ] (s : Finset α) (p : α → ℝ)
    (g : α → γ) (hp : ∀ a ∈ s, 0 < p a) {b : γ} (hb : b ∈ s.image g) :
    0 < mass s p g b := by
  classical
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact (hp a ha).trans_le (Finset.single_le_sum
    (fun x hx => (hp x (Finset.mem_filter.mp hx).1).le) (by simp [ha]))

theorem cellMass_eq (p : α → ℝ) (g : α → β) {k : ℕ} (c : Fin k → β) (i : Fin k) :
    ProductLaw.cellMass (fun _ : Fin k => p) (fun _ => g) c i = mass Finset.univ p g (c i) := by
  simp only [ProductLaw.cellMass, mass, Finset.sum_filter]

theorem conditional_mean_eq (p : α → ℝ) (v : α → ℝ) (g : α → β)
    {k : ℕ} (c : Fin k → β) (i : Fin k) :
    (∑ a, ProductLaw.conditional (fun _ : Fin k => p) (fun _ => g) c i a * v a) =
      cellMean p v g (c i) := by
  simp only [cellMean, ProductLaw.conditional, cellMass_eq]

theorem conditional_mean_distance_le (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 ≤ p a) {k : ℕ} (c : Fin k → β) (i : Fin k)
    (hc : mass Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => g (x i)) c ≠ 0) (x : α) (hx : g x = c i) (R : ℝ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ R) :
    |v x-cellMean p v g (c i)| ≤ R := by
  rw [← conditional_mean_eq p v g c i]
  apply distance_mean_le _ _ _ R
    (ProductLaw.conditional_nonneg _ _ _ (fun _ a => hp a) i)
    (ProductLaw.conditional_sum _ _ _ hc i)
  intro a ha
  have hga : g a = c i := by
    by_contra hn
    exact ha (by simp only [ProductLaw.conditional, ite_eq_right hn, zero_div])
  exact hd x a (hx.trans hga.symm)

theorem fiber_entropy_hit_bound (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ) (u : AddCircle (1 : ℝ))
    (c : Fin k → β)
    (hc : c ∈ (Finset.univ : Finset (Fin k → α)).image (fun x i => g (x i))) :
    conditionalEntropy (Finset.univ.filter (fun x : Fin k → α => (fun i => g (x i)) = c))
      (fun x => ProductLaw.weight (fun _ : Fin k => p) x /
        mass Finset.univ (ProductLaw.weight (fun _ : Fin k => p)) (fun x i => g (x i)) c)
      (fun x i => RandomGrid.cell δ u (v (x i))) (fun x => ∑ i, v (x i)) ≤
    11*k*(∑ x ∈ Finset.univ.filter (fun x : Fin k → α => (fun i => g (x i)) = c),
      (ProductLaw.weight (fun _ : Fin k => p) x /
        mass Finset.univ (ProductLaw.weight (fun _ : Fin k => p)) (fun x i => g (x i)) c) *
      ∑ i, ∑ j, RandomGrid.hit (-(cellMean p v g (c j)/δ : ℝ) : AddCircle (1 : ℝ))
        (4*k*|v (x i)-cellMean p v g (c i)|/δ) u)*Real.log 2 := by
  classical
  let w : (Fin k → α) → ℝ := ProductLaw.weight (fun _ : Fin k => p)
  let G : (Fin k → α) → (Fin k → β) := fun x i => g (x i)
  have hw : ∀ x : Fin k → α, 0 < w x := fun x => Finset.prod_pos (fun i _ => hp (x i))
  have hP : 0 < mass Finset.univ w G c := mass_pos Finset.univ w G (fun x _ => hw x) hc
  have hnc : mass Finset.univ w G c ≠ 0 := ne_of_gt hP
  let s₀ : Finset (Fin k → α) := Finset.univ.filter (fun x => G x = c)
  let p₀ : (Fin k → α) → ℝ := fun x => w x / mass Finset.univ w G c
  let v₀ : (Fin k → α) → Fin k → ℝ := fun x i => v (x i)
  let m₀ : Fin k → ℝ := fun i => cellMean p v g (c i)
  have hp₀ : ∀ x ∈ s₀, 0 ≤ p₀ x := fun x _ => div_nonneg (hw x).le hP.le
  have hp₀1 : ∑ x ∈ s₀, p₀ x = 1 := by
    rw [show (∑ x ∈ s₀, p₀ x) = mass Finset.univ w G c / mass Finset.univ w G c by
      exact (Finset.sum_div _ _ _).symm]
    exact div_self hnc
  have hv₀ : ∀ x ∈ s₀, ∀ i, |v₀ x i-m₀ i| ≤ 4*δ := by
    intro x hx i
    have he : G x = c := (Finset.mem_filter.mp hx).2
    exact conditional_mean_distance_le p v g (fun a => (hp a).le) c i hnc (x i)
      (congrFun he i) (4*δ) hd
  have hind : ∀ a : ℝ, ∀ i j : Fin k, i ≠ j →
      (∑ x ∈ s₀, if a/(4*k) ≤ |v₀ x i-m₀ i| ∧ a/(4*k) ≤ |v₀ x j-m₀ j| then p₀ x else 0) =
      (∑ x ∈ s₀, if a/(4*k) ≤ |v₀ x i-m₀ i| then p₀ x else 0) *
      (∑ x ∈ s₀, if a/(4*k) ≤ |v₀ x j-m₀ j| then p₀ x else 0) := by
    intro a i j hij
    let E := fun (i : Fin k) (x : α) => a/(4*k) ≤ |v x-cellMean p v g (c i)|
    have heen := ProductLaw.two_coordinate_events
      (ProductLaw.conditional (fun _ : Fin k => p) (fun _ => g) c) E
      (ProductLaw.conditional_sum _ _ _ hnc) i j hij
    rw [← ProductLaw.conditional_event (fun _ : Fin k => p) (fun _ => g) c (fun x => E i (x i) ∧ E j (x j)),
      ← ProductLaw.conditional_event (fun _ : Fin k => p) (fun _ => g) c (fun x => E i (x i)),
      ← ProductLaw.conditional_event (fun _ : Fin k => p) (fun _ => g) c (fun x => E j (x j))] at heen
    exact heen
  exact RandomGrid.refinement_entropy_hit_bound s₀ p₀ k hk v₀ m₀ δ hδ u hp₀ hp₀1 hv₀ hind

theorem entropy_step_hit_bound (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a)
    (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ)
    (u : AddCircle (1 : ℝ)) :
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) ≤
    11*k*(∑ x : Fin k → α, ProductLaw.weight (fun _ : Fin k => p) x * ∑ i, ∑ j,
      RandomGrid.hit (-(cellMean p v g (g (x j))/δ : ℝ) : AddCircle (1 : ℝ))
        (4*k*|v (x i)-cellMean p v g (g (x i))|/δ) u)*Real.log 2 := by
  classical
  let w := ProductLaw.weight (fun _ : Fin k => p)
  let G := fun (x : Fin k → α) i => g (x i)
  let Y := fun (x : Fin k → α) => ∑ i, v (x i)
  let C := fun (x : Fin k → α) i => RandomGrid.cell δ u (v (x i))
  let P := mass Finset.univ w G
  let M := fun (c : Fin k → β) i => cellMean p v g (c i)
  let cost := fun (c : Fin k → β) (x : Fin k → α) => ∑ i, ∑ j,
    RandomGrid.hit (-(M c j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v (x i)-M c i|/δ) u
  have hw : ∀ x : Fin k → α, 0 < w x := fun x => Finset.prod_pos (fun i _ => hp (x i))
  have hP : ∀ c ∈ Finset.univ.image G, 0 < P c :=
    fun c hc => mass_pos Finset.univ w G (fun x _ => hw x) hc
  have hcstep : ∀ c ∈ Finset.univ.image G,
      conditionalEntropy (Finset.univ.filter (fun x => G x = c)) (fun x => w x/P c) C Y ≤
        11*k*(∑ x ∈ Finset.univ.filter (fun x => G x = c), (w x/P c)*cost c x)*Real.log 2 :=
    fun c hc => fiber_entropy_hit_bound p v g hp k hk δ hδ hd u c hc
  rw [conditionalEntropy_disintegrate Finset.univ w C G Y (fun x _ => (hw x).le)]
  calc
    _ ≤ ∑ c ∈ Finset.univ.image G, P c *
        (11*k*(∑ x ∈ Finset.univ.filter (fun x => G x = c), (w x/P c)*cost c x)*Real.log 2) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcstep c hc) (hP c hc).le
    _ = 11*k*(∑ c ∈ Finset.univ.image G,
        ∑ x ∈ Finset.univ.filter (fun x => G x = c), w x*cost (G x) x)*Real.log 2 := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
      field_simp [ne_of_gt (hP c hc)]
    _ = _ := by
      rw [Finset.sum_fiberwise_of_maps_to (fun x (_ : x ∈ Finset.univ) => Finset.mem_image_of_mem G (Finset.mem_univ x))]

theorem product_mean_deviation (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp1 : ∑ a, p a = 1) (k : ℕ) :
    (∑ x : Fin k → α, ProductLaw.weight (fun _ : Fin k => p) x *
      ∑ i, |v (x i)-cellMean p v g (g (x i))|) =
      k * ∑ a, p a*|v a-cellMean p v g (g a)| := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ i : Fin k, (∑ x : Fin k → α, ProductLaw.weight (fun _ : Fin k => p) x *
      |v (x i)-cellMean p v g (g (x i))|) = ∑ a, p a*|v a-cellMean p v g (g a)| := by
    intro i
    simpa only [Finset.prod_singleton] using ProductLaw.moment (fun _ : Fin k => p)
      (fun _ a => |v a-cellMean p v g (g a)|) {i} (fun _ => hp1)
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem exists_entropy_step (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1)
    (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ) :
    ∃ u : AddCircle (1 : ℝ),
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) ≤
    (88*k^4/δ)*(∑ a, p a*|v a-cellMean p v g (g a)|)*Real.log 2 := by
  classical
  obtain ⟨u,hu⟩ := RandomGrid.exists_shift_variation_bound Finset.univ
    (ProductLaw.weight (fun _ : Fin k => p)) k (fun x i => v (x i))
    (fun x i => cellMean p v g (g (x i))) δ hδ
    (fun x _ => ProductLaw.weight_nonneg _ (fun _ a => (hp a).le) x)
  refine ⟨u, (entropy_step_hit_bound p v g hp k hk δ hδ hd u).trans ?_⟩
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ (11 : ℝ)*k))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  rw [product_mean_deviation p v g hp1 k] at hm
  convert hm using 1; ring

end FiniteRefinement

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteRefinement
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteRefinement.exists_entropy_step.{uα,uβ} := @_root_.OAI.EntropyRateDimension.FiniteRefinement.exists_entropy_step.{uα,uβ}
