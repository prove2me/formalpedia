-- Prove2me | solution 1 for OAI.Erdos3.affine_mesh_scalar_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T18:12:10.257417+00:00
-- url     : https://prove2.me/submissions/76669fbe-5b1f-4a01-93ba-c0d89528e3e2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_primeCoordinateReference_weight_pos
import Theorems.Thm_OAI_Erdos3_residueTruncationCap_nonneg

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace FiniteProbabilityWeights

variable (p : FiniteProbabilityWeights Ω) (G : Finset Ω)

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X C : Type*} [Fintype X] [MeasurableSpace C] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] (law : FiniteProbabilityWeights I)
variable (P : I → Prop) (hP : ∀ i, P i ↔ 0 < law.weight i)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

variable {Ω R : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω) (F : Ω → R)

theorem fiberMean_le_mul_mass (f : Ω → ℝ) (M : ℝ) (hf : ∀ z, f z ≤ M) (y : R) :
    p.fiberMean F y f ≤ M * p.fiberMean F y (fun _ => 1) := by
  classical
  unfold fiberMean
  rw [← p.mean_const_mul]
  apply p.mean_mono
  intro z
  by_cases hz : F z = y
  · simpa only [hz, ite_true, mul_one] using hf z
  · simp only [hz, ite_false, mul_zero, le_refl]

theorem fiberMean_zero_of_mass_zero (f : Ω → ℝ) (M : ℝ)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (y : R)
    (hy : p.fiberMean F y (fun _ => 1) = 0) : p.fiberMean F y f = 0 := by
  have h0 := p.fiberMean_nonneg F y f (fun z => (hf z).1)
  have h1 := p.fiberMean_le_mul_mass F f M (fun z => (hf z).2) y
  rw [hy, mul_zero] at h1
  exact le_antisymm h1 h0

theorem fiberTest_bounds (f : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (y : R) :
    0 ≤ p.fiberTest F f y ∧ p.fiberTest F f y ≤ M := by
  have hmass := p.fiberMean_nonneg F y (fun _ => 1) (fun _ => zero_le_one)
  constructor
  · exact div_nonneg (p.fiberMean_nonneg F y f (fun z => (hf z).1)) hmass
  · by_cases hy : p.fiberMean F y (fun _ => 1) = 0
    · simpa only [fiberTest, hy, div_zero] using hM
    · have hp : 0 < p.fiberMean F y (fun _ => 1) := lt_of_le_of_ne hmass (Ne.symm hy)
      exact (div_le_iff₀ hp).mpr (p.fiberMean_le_mul_mass F f M (fun z => (hf z).2) y)

theorem mass_mul_fiberTest (f : Ω → ℝ) (M : ℝ) (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (y : R) :
    p.fiberMean F y (fun _ => 1) * p.fiberTest F f y = p.fiberMean F y f := by
  by_cases hy : p.fiberMean F y (fun _ => 1) = 0
  · rw [hy, zero_mul, p.fiberMean_zero_of_mass_zero F f M hf y hy]
  · unfold fiberTest
    field_simp

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem productCoordinateMix_univ [Fintype I] (x y : ∀ i, X i) :
    productCoordinateMix Finset.univ x y = x := by
  funext i
  simp [productCoordinateMix]

theorem productCoordinateMix_comp (S T : Finset I) (x y z : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix S x y) z =
      productCoordinateMix (S ∩ T) x (productCoordinateMix T y z) := by
  funext i
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
    simp [productCoordinateMix, hs, ht]

variable [Fintype I] [∀ i, Fintype (X i)]

theorem productCoordinateMix_weight (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (x y : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S x y) *
      (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S y x) =
        (FiniteProbabilityWeights.pi μ).weight x * (FiniteProbabilityWeights.pi μ).weight y := by
  change (∏ i, (μ i).weight (productCoordinateMix S x y i)) *
      (∏ i, (μ i).weight (productCoordinateMix S y x i)) =
    (∏ i, (μ i).weight (x i)) * (∏ i, (μ i).weight (y i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi, mul_comm]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem eventProbability_le_of_weight_le {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) (C : ℝ)
    (hw : ∀ x, p.weight x ≤ C * q.weight x) (E : Ω → Prop) :
    p.eventProbability E ≤ C * q.eventProbability E := by
  classical
  unfold eventProbability mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x <;> simp [hx, hw x]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem productMean_coordinateSwap (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (F : (∀ i, X i) → (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => F (productCoordinateMix S x y) (productCoordinateMix S y x))) =
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean (F x)) := by
  let p := FiniteProbabilityWeights.pi μ
  have h : (∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 *
        F (productCoordinateMix S z.1 z.2) (productCoordinateMix S z.2 z.1)) =
      ∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 * F z.1 z.2 := by
    apply Fintype.sum_equiv (productCoordinateSwap (X := X) S)
    intro z
    change _ = p.weight (productCoordinateMix S z.1 z.2) *
      p.weight (productCoordinateMix S z.2 z.1) * _
    rw [productCoordinateMix_weight]
    rfl
  simpa only [FiniteProbabilityWeights.mean, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc] using h

theorem productMean_coordinateMix (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => f (productCoordinateMix S x y))) = (FiniteProbabilityWeights.pi μ).mean f := by
  have h := productMean_coordinateSwap μ S (fun x _ => f x)
  simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem fixedParameter_observed_tail_of_tests
    {X T A : Type*} [Fintype X] [Fintype T]
    (source : FiniteProbabilityWeights X) (parameter : FiniteProbabilityWeights T)
    (observe : X → A) (value : T → A → ℝ) {gap bound : ℝ} (hgap : 0 < gap)
    (htest : ∀ w : A → ℝ, (∀ x, 0 ≤ w (observe x) ∧ w (observe x) ≤ 1) →
      (parameter.prod source).mean (fun tx => w (observe tx.2) * value tx.1 (observe tx.2)) ≤ gap * bound) :
    source.eventProbability (fun x => gap < parameter.mean (fun t => value t (observe x))) ≤ bound := by
  let w : A → ℝ := fun z => if gap < parameter.mean (fun t => value t z) then 1 else 0
  have hw (x) : 0 ≤ w (observe x) ∧ w (observe x) ≤ 1 := by
    dsimp only [w]
    split_ifs <;> norm_num
  have hup := htest w hw
  rw [FiniteProbabilityWeights.mean_prod, FiniteProbabilityWeights.mean_comm] at hup
  simp only [FiniteProbabilityWeights.mean_const_mul] at hup
  have hlow : gap * source.eventProbability
      (fun x => gap < parameter.mean (fun t => value t (observe x))) ≤
      source.mean (fun x => w (observe x) * parameter.mean (fun t => value t (observe x))) := by
    rw [FiniteProbabilityWeights.eventProbability, ← source.mean_const_mul]
    apply source.mean_mono
    intro x
    dsimp only [w]
    split_ifs with hx
    · simpa only [mul_one, one_mul] using hx.le
    · simp only [mul_zero, zero_mul, le_refl]
  exact (mul_le_mul_iff_right₀ hgap).mp (hlow.trans hup)

theorem fixedParameter_observed_tail_exp
    {X T A : Type*} [Fintype X] [Fintype T]
    (source : FiniteProbabilityWeights X) (parameter : FiniteProbabilityWeights T)
    (observe : X → A) (value : T → A → ℝ) (p dominationLog : ℝ)
    (htest : ∀ w : A → ℝ, (∀ x, 0 ≤ w (observe x) ∧ w (observe x) ≤ 1) →
      (parameter.prod source).mean (fun tx => w (observe tx.2) * value tx.1 (observe tx.2)) ≤
        Real.exp (-(2 * p + dominationLog)) / 2) :
    source.eventProbability (fun x => Real.exp (-p) < parameter.mean (fun t => value t (observe x))) ≤
      Real.exp (-(p + dominationLog)) := by
  apply fixedParameter_observed_tail_of_tests source parameter observe value (Real.exp_pos (-p))
  intro w hw
  apply (htest w hw).trans
  rw [← Real.exp_add]
  have he : -p + -(p + dominationLog) = -(2 * p + dominationLog) := by ring
  rw [he]
  linarith [Real.exp_pos (-(2 * p + dominationLog))]

theorem fixedParameter_observed_tail_dominated
    {X T A : Type*} [Fintype X] [Fintype T]
    (source outer : FiniteProbabilityWeights X) (parameter : FiniteProbabilityWeights T)
    (observe : X → A) (value : T → A → ℝ) (p dominationLog : ℝ)
    (hdom : ∀ x, outer.weight x ≤ Real.exp dominationLog * source.weight x)
    (htest : ∀ w : A → ℝ, (∀ x, 0 ≤ w (observe x) ∧ w (observe x) ≤ 1) →
      (parameter.prod source).mean (fun tx => w (observe tx.2) * value tx.1 (observe tx.2)) ≤
        Real.exp (-(2 * p + dominationLog)) / 2) :
    outer.eventProbability (fun x => Real.exp (-p) < parameter.mean (fun t => value t (observe x))) ≤
      Real.exp (-p) := by
  have ht := fixedParameter_observed_tail_exp source parameter observe value p dominationLog htest
  calc
    _ ≤ Real.exp dominationLog * source.eventProbability
        (fun x => Real.exp (-p) < parameter.mean (fun t => value t (observe x))) :=
      outer.eventProbability_le_of_weight_le source _ hdom _
    _ ≤ Real.exp dominationLog * Real.exp (-(p + dominationLog)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_univ (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ Finset.univ f x = f x := by
  simp only [productConditionalMean, productCoordinateMix_univ,
    FiniteProbabilityWeights.mean_const]

theorem productConditionalMean_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => c * f y) x = c * productConditionalMean μ S f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul _ _

theorem productConditionalMean_sum {J : Type*} (s : Finset J) (S : Finset I)
    (f : J → (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, productConditionalMean μ S (f j) x :=
  (FiniteProbabilityWeights.pi μ).mean_sum _ _

theorem productConditionalMean_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productConditionalMean μ S f) := by
  intro x y hxy
  unfold productConditionalMean
  congr 1
  funext z
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [productCoordinateMix, hi, hxy i hi]
  · simp [productCoordinateMix, hi]

theorem productConditionalMean_of_depends (S : Finset I) {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (x : ∀ i, X i) : productConditionalMean μ S f x = f x := by
  have hpoint (y : ∀ i, X i) : f (productCoordinateMix S x y) = f x := by
    apply hf
    intro i hi
    simp [productCoordinateMix, hi]
  simp only [productConditionalMean, hpoint, FiniteProbabilityWeights.mean_const]

theorem productConditionalMean_comp (S T : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (productConditionalMean μ T f) x =
      productConditionalMean μ (S ∩ T) f x := by
  simp only [productConditionalMean, productCoordinateMix_comp]
  exact productMean_coordinateMix μ T (fun y => f (productCoordinateMix (S ∩ T) x y))

theorem productConditionalMean_selfadjoint (S : Finset I) (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productConditionalMean μ S g x) =
      (FiniteProbabilityWeights.pi μ).mean (fun x => productConditionalMean μ S f x * g x) := by
  have h := productMean_coordinateSwap μ S
    (fun x y => f x * g (productCoordinateMix S x y))
  simp only [productCoordinateMix_swap] at h
  unfold productConditionalMean
  simp_rw [← FiniteProbabilityWeights.mean_const_mul, ← FiniteProbabilityWeights.mean_mul_const]
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem finiteWeightDensity_nonneg (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (x : Ω) : 0 ≤ finiteWeightDensity p w x :=
  div_nonneg (hw x) (p.nonneg x)

theorem finiteWeightDensity_mul (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (hsupport : ∀ x, p.weight x = 0 → w x = 0) (x : Ω) :
    p.weight x * finiteWeightDensity p w x = w x := by
  by_cases hx : p.weight x = 0
  · rw [hx, zero_mul, hsupport x hx]
  · unfold finiteWeightDensity
    field_simp

theorem mean_finiteWeightDensity (p : FiniteProbabilityWeights Ω) (w f : Ω → ℝ)
    (hsupport : ∀ x, p.weight x = 0 → w x = 0) :
    p.mean (fun x => finiteWeightDensity p w x * f x) = ∑ x, w x * f x := by
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, finiteWeightDensity_mul p w hsupport]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniform_subtype_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    (FiniteProbabilityWeights.uniform Ω).mean (fun z => if P z then f z else 0) =
      (Fintype.card {z // P z} : ℝ) / Fintype.card Ω * (𝔼 z : {z // P z}, f z.val) := by
  classical
  rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
  have hsum : (∑ z, if P z then f z else 0) = ∑ z : {z // P z}, f z.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  rw [hsum, ← Fintype.card_mul_expect (fun z : {z // P z} => f z.val)]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteCellMean_uniform {X A : Type*} [Fintype X] [Nonempty X] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X *
        (𝔼 x : {x // C x = a}, f x.val) :=
  uniform_subtype_mean (fun x => C x = a) f

theorem finiteCellWeights_uniform {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (a : A) :
    (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X := by
  change finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun _ => 1) a = _
  rw [finiteCellMean_uniform]
  by_cases h : Nonempty {x // C x = a}
  · let : Nonempty {x // C x = a} := h
    simp
  · let : IsEmpty {x // C x = a} := not_nonempty_iff.mp h
    simp

theorem finiteCellMean_uniform_weighted {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a *
        (𝔼 x : {x // C x = a}, f x.val) := by
  rw [finiteCellWeights_uniform, finiteCellMean_uniform]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {X T A B : Type*} [Fintype X] [Fintype T] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

omit [Fintype A] [Fintype B] in
theorem finiteCellMean_product (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights T)
    (C : X → A) (E : T → B) (f : X → T → ℝ) (a : A) (b : B) :
    finiteCellMean (q.prod p) (fun tx => (C tx.2, E tx.1)) (fun tx => f tx.2 tx.1) (a,b) =
      finiteCellMean p C (fun x => finiteCellMean q E (f x) b) a := by
  unfold finiteCellMean
  rw [FiniteProbabilityWeights.mean_prod, FiniteProbabilityWeights.mean_comm]
  congr 1
  funext x
  by_cases hx : C x = a
  · simp only [hx, Prod.mk.injEq, true_and, ite_true]
  · have he (t : T) : (if (C x, E t) = (a,b) then f x t else 0) = 0 := by
      simp [hx]
    simp only [he, q.mean_const, if_neg hx]

theorem finiteCellWeights_product (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights T)
    (C : X → A) (E : T → B) (a : A) (b : B) :
    (finiteCellWeights (q.prod p) (fun tx => (C tx.2, E tx.1))).weight (a,b) =
      (finiteCellWeights p C).weight a * (finiteCellWeights q E).weight b := by
  change finiteCellMean (q.prod p) _ (fun _ => 1) (a,b) = _
  rw [finiteCellMean_product p q C E (fun _ _ => 1)]
  change p.mean (fun x => if C x = a then (finiteCellWeights q E).weight b else 0) = _
  have he : (fun x => if C x = a then (finiteCellWeights q E).weight b else 0) =
      (fun x => (if C x = a then 1 else 0) * (finiteCellWeights q E).weight b) := by
    funext x
    split_ifs <;> simp
  rw [he, p.mean_mul_const]
  rfl

theorem finiteCellMean_product_uniform [Nonempty X] [Nonempty T]
    (C : X → A) (E : T → B) (f : X → T → ℝ) (a : A) (b : B) :
    finiteCellMean ((FiniteProbabilityWeights.uniform T).prod (FiniteProbabilityWeights.uniform X))
      (fun tx => (C tx.2, E tx.1)) (fun tx => f tx.2 tx.1) (a,b) =
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a *
        (finiteCellWeights (FiniteProbabilityWeights.uniform T) E).weight b *
        (𝔼 x : {x // C x = a}, 𝔼 t : {t // E t = b}, f x.val t.val) := by
  rw [finiteCellMean_product]
  simp only [finiteCellMean_uniform_weighted]
  rw [← Finset.mul_expect]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem physicalBoxCell_subset (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (c : ∀ i, (P i).Label) :
    translatedIntegerBox (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => (P i).length (c i)) ⊆
      translatedIntegerBox lo N := by
  intro x hx
  apply (mem_translatedIntegerBox lo N x).mpr
  intro i
  have hi := (mem_translatedIntegerBox _ _ x).mp hx i
  have hend : ((P i).start (c i) : ℤ) + (P i).length (c i) ≤ N i := by
    exact_mod_cast (P i).end_le_of_step_one (hstep i) (c i) (hpos i (c i))
  have hstart : (0 : ℤ) ≤ (P i).start (c i) := Int.natCast_nonneg _
  dsimp only [intervalCellLower] at hi
  constructor <;> omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem realZeroExtendFinset_on {X : Type*} (S : Finset X) (f : X → ℝ)
    {x : X} (hx : x ∈ S) : realZeroExtendFinset S f x = f x := by
  simp only [realZeroExtendFinset, if_pos hx]

theorem realZeroExtendFinset_off {X : Type*} (S : Finset X) (f : X → ℝ)
    {x : X} (hx : x ∉ S) : realZeroExtendFinset S f x = 0 := by
  simp only [realZeroExtendFinset, if_neg hx]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem retained_mesh_cell_constant {I X M : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (mesh : X → M) (location : X → I → ℤ) (x : X)
    (hx : ¬ physicalMeshCrossing lo N P mesh location x) :
    ∀ y, mesh y = mesh x → physicalBoxClassify lo N P (location y) = physicalBoxClassify lo N P (location x) := by
  intro y hy
  by_contra h
  exact hx ⟨y, hy, Ne.symm h⟩

theorem physicalMeshCrossing_congr {I X M : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (mesh : X → M) (location : X → I → ℤ) {x y : X} (hxy : mesh x = mesh y) :
    physicalMeshCrossing lo N P mesh location x ↔ physicalMeshCrossing lo N P mesh location y := by
  have transfer (u v : X) (huv : mesh u = mesh v)
      (hu : physicalMeshCrossing lo N P mesh location u) : physicalMeshCrossing lo N P mesh location v := by
    obtain ⟨z, hz, huz⟩ := hu
    by_cases hvz : physicalBoxClassify lo N P (location v) = physicalBoxClassify lo N P (location z)
    · exact ⟨u, huv, fun hvu => huz (hvu.symm.trans hvz)⟩
    · exact ⟨z, hz.trans huv, hvz⟩
  exact ⟨transfer x y hxy, transfer y x hxy.symm⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

theorem mem_lowDegreeCoordinateSets (b : ℕ) (S : Finset I) :
    S ∈ lowDegreeCoordinateSets I b ↔ S.card ≤ b := by
  simp only [lowDegreeCoordinateSets, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨j, hj, hcard⟩
    omega
  · intro h
    exact ⟨S.card, by omega, rfl⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMarginalAtomError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMarginal_test_error (r g : (∀ i, X i) → ℝ) (S : Finset I)
    {η C : ℝ} (hη : 0 ≤ η) (hg : ProductDependsOn S g)
    (hr : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ S r x - 1| ≤ η)
    (hcap : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |g x| ≤ C) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * g x) -
      (FiniteProbabilityWeights.pi μ).mean g| ≤ η * C := by
  let p := FiniteProbabilityWeights.pi μ
  have he := productConditionalMean_selfadjoint μ S r g
  simp_rw [productConditionalMean_of_depends μ S hg] at he
  have hid : p.mean (fun x => r x * g x) - p.mean g =
      p.mean (fun x => (productConditionalMean μ S r x - 1) * g x) := by
    rw [he, ← p.mean_sub]
    congr 1
    funext x
    ring
  rw [hid]
  apply p.abs_mean_le_on_support
  intro x hx
  rw [abs_mul]
  exact mul_le_mul (hr x hx) (hcap x hx) (abs_nonneg _) hη

theorem productConditionalMean_weighted_cap (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (S : Finset I) (x : ∀ i, X i) :
    0 ≤ productConditionalMean μ S (fun y => r y * f y) x ∧
      productConditionalMean μ S (fun y => r y * f y) x ≤ M * productConditionalMean μ S r x := by
  constructor
  · exact (FiniteProbabilityWeights.pi μ).mean_nonneg (fun y =>
      mul_nonneg (hr _) (hf _).1)
  · unfold productConditionalMean
    rw [← FiniteProbabilityWeights.mean_const_mul]
    apply FiniteProbabilityWeights.mean_mono
    intro y
    simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hf _).2 (hr _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubsetAlternatingInversion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

theorem subsetAlternatingTransform_insert (F : Finset ι → ℝ) (S : Finset ι)
    {i : ι} (hi : i ∉ S) :
    subsetAlternatingTransform F (insert i S) =
      subsetAlternatingTransform (fun T => F (insert i T)) S - subsetAlternatingTransform F S := by
  unfold subsetAlternatingTransform
  rw [Finset.sum_powerset_insert hi]
  have he₁ (U : Finset ι) (hU : U ∈ S.powerset) : (insert i S) \ U = insert i (S \ U) := by
    have hn : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
    ext j
    by_cases hj : j = i <;> simp [hj, hn]
  have he₂ (U : Finset ι) (hU : U ∈ S.powerset) :
      (-1 : ℝ) ^ (insert i U).card * F ((insert i S) \ insert i U) =
        -((-1 : ℝ) ^ U.card * F (S \ U)) := by
    have hn : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
    have hs : (insert i S) \ insert i U = S \ U := by
      ext j
      by_cases hj : j = i <;> simp [hj, hi]
    rw [hs, Finset.card_insert_of_notMem hn, pow_succ]
    ring
  rw [Finset.sum_congr rfl (fun U hU => congrArg (fun z => (-1 : ℝ) ^ U.card * F z) (he₁ U hU)),
    Finset.sum_congr rfl he₂, Finset.sum_neg_distrib]
  rfl

theorem subsetAlternatingTransform_sum (S : Finset ι) (F : Finset ι → ℝ) :
    (∑ T ∈ S.powerset, subsetAlternatingTransform F T) = F S := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp [subsetAlternatingTransform]
  | @insert i S hi ih =>
      rw [Finset.sum_powerset_insert hi]
      have he (T : Finset ι) (hT : T ∈ S.powerset) :
          subsetAlternatingTransform F (insert i T) =
            subsetAlternatingTransform (fun U => F (insert i U)) T - subsetAlternatingTransform F T :=
        subsetAlternatingTransform_insert F T (fun h => hi (Finset.mem_powerset.mp hT h))
      rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, ih F, ih (fun U => F (insert i U))]
      ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem alternating_powerset_sum_zero {I : Type*} [DecidableEq I]
    (S : Finset I) {i : I} (hi : i ∈ S) (g : Finset I → ℝ)
    (hpair : ∀ U ⊆ S.erase i, g (insert i U) = g U) :
    (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * g U) = 0 := by
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i S), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro U hU
  have hu := Finset.mem_powerset.mp hU
  have hni : i ∉ U := fun h => Finset.notMem_erase i S (hu h)
  rw [Finset.card_insert_of_notMem hni, pow_succ, hpair U hu]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productANOVA μ S f) := by
  intro x y hxy
  unfold productANOVA
  apply Finset.sum_congr rfl
  intro U _
  congr 1
  exact productConditionalMean_depends μ (S \ U) f x y
    (fun i hi => hxy i (Finset.sdiff_subset hi))

theorem productConditionalMean_ANOVA (S T : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ T (productANOVA μ S f) x =
      if S ⊆ T then productANOVA μ S f x else 0 := by
  classical
  change productConditionalMean μ T (fun y => ∑ U ∈ S.powerset,
    (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f y) x =
      if S ⊆ T then (∑ U ∈ S.powerset,
        (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x) else 0
  simp only [productConditionalMean_sum, productConditionalMean_smul, productConditionalMean_comp]
  by_cases hST : S ⊆ T
  · rw [if_pos hST]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.inter_eq_right.mpr (Finset.sdiff_subset.trans hST)]
  · rw [if_neg hST]
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hST
    apply alternating_powerset_sum_zero S hi
    intro U _
    have he : T ∩ (S \ insert i U) = T ∩ (S \ U) := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [hni]
      · simp [hj]
    rw [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_orthogonal_of_not_subset (S T : Finset I) (hTS : ¬ T ⊆ S)
    (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x * productANOVA μ T g x) = 0 := by
  have h := productConditionalMean_selfadjoint μ S (productANOVA μ S f) (productANOVA μ T g)
  simpa [productConditionalMean_ANOVA, hTS, FiniteProbabilityWeights.mean_const] using h.symm

theorem productANOVA_orthogonal (S T : Finset I) (hST : S ≠ T)
    (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x * productANOVA μ T g x) = 0 := by
  by_cases hTS : T ⊆ S
  · have hn : ¬ S ⊆ T := fun h => hST (Finset.Subset.antisymm h hTS)
    simpa only [mul_comm] using productANOVA_orthogonal_of_not_subset μ T S hn g f
  · exact productANOVA_orthogonal_of_not_subset μ S T hTS f g

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_abs_le (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) {L : ℝ}
    (hraw : ∀ T ⊆ S, |productConditionalMean μ T f x| ≤ L) :
    |productANOVA μ S f x| ≤ (2 : ℝ) ^ S.card * L := by
  unfold productANOVA
  calc
    _ ≤ ∑ U ∈ S.powerset, |(-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _U ∈ S.powerset, L := by
      apply Finset.sum_le_sum
      intro U _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        hraw (S \ U) Finset.sdiff_subset
    _ = _ := by simp

theorem productANOVA_weighted_cap (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M η : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (S : Finset I)
    (hclose : ∀ T ⊆ S, ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ T r x - 1| ≤ η)
    (x : ∀ i, X i) (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    |productANOVA μ S (fun y => r y * f y) x| ≤ (2 : ℝ) ^ S.card * (M * (1 + η)) := by
  apply productANOVA_abs_le μ S _ x
  intro T hT
  have hc := productConditionalMean_weighted_cap μ r f hr hf T x
  rw [abs_of_nonneg hc.1]
  have he := (abs_le.mp (hclose T hT x hx)).2
  exact hc.2.trans (mul_le_mul_of_nonneg_left (by linarith) hM)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_reconstruct (S : Finset ι) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    (∑ T ∈ S.powerset, productANOVA μ T f x) = productConditionalMean μ S f x :=
  subsetAlternatingTransform_sum S (fun T => productConditionalMean μ T f x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_nonneg (f : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) (x : ∀ i, X i) :
    0 ≤ observedProductDensity μ p F f x := by
  apply finiteWeightDensity_nonneg
  intro y
  exact p.fiberMean_nonneg F y f hf

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_factor (w : Ω → ℝ) (M : ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) (x : ∀ i, X i) :
    observedProductDensity μ p F w x =
      observedProductDensity μ p F (fun _ => 1) x * p.fiberTest F w x := by
  change p.fiberMean F x w / (FiniteProbabilityWeights.pi μ).weight x =
    (p.fiberMean F x (fun _ => 1) / (FiniteProbabilityWeights.pi μ).weight x) * p.fiberTest F w x
  rw [← p.mass_mul_fiberTest F w M hw x]
  ring

theorem observedProductDensity_bounded_factor (w : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) :
    ∃ f : (∀ i, X i) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
      observedProductDensity μ p F w = (fun x => observedProductDensity μ p F (fun _ => 1) x * f x) := by
  exact ⟨p.fiberTest F w, p.fiberTest_bounds F w M hM hw,
    funext (observedProductDensity_factor μ p F w M hw)⟩

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
  (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

include hμ

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem FiniteProbabilityWeights.mean_fiber_factor {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (p : FiniteProbabilityWeights Ω) (F : Ω → Y) (w : Ω → ℝ) (a : Y → ℝ) :
    p.mean (fun z => w z * a (F z)) = ∑ y, p.fiberMean F y w * a y := by
  unfold FiniteProbabilityWeights.fiberMean FiniteProbabilityWeights.mean
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [mul_ite, ite_mul, mul_assoc]

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_test (hμ : ∀ i x, 0 < (μ i).weight x)
    (w : Ω → ℝ) (a : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => observedProductDensity μ p F w x * a x) =
      p.mean (fun z => w z * a (F z)) := by
  unfold observedProductDensity
  rw [mean_finiteWeightDensity]
  · exact (p.mean_fiber_factor F w a).symm
  · intro x hx
    exact False.elim ((Finset.prod_pos (fun i _ => hμ i (x i))).ne' hx)

theorem observedProductDensity_component_cap (hμ : ∀ i x, 0 < (μ i).weight x)
    (w : Ω → ℝ) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) {b : ℕ}
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) eta b)
    (S : Finset ι) (hS : S.card ≤ b) (x : ∀ i, X i) :
    |productANOVA μ S (observedProductDensity μ p F w) x| ≤ (2 : ℝ) ^ b * M * (1 + eta) := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w M hM hw
  rw [he]
  have hc := productANOVA_weighted_cap μ (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (fun _ => zero_le_one)) hM hf S
    (fun T hT => hclose T ((Finset.card_le_card hT).trans hS)) x
    (Finset.prod_pos (fun i _ => hμ i (x i))).ne'
  have hp : (2 : ℝ) ^ S.card ≤ (2 : ℝ) ^ b := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) hS
  calc
    _ ≤ (2 : ℝ) ^ S.card * (M * (1 + eta)) := hc
    _ ≤ (2 : ℝ) ^ b * (M * (1 + eta)) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductEquivTransport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

omit [Fintype ι] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] in
theorem productCoordinateMix_map (F : ∀ i, X i → Y i) (S : Finset ι) (x y : ∀ i, X i) :
    (fun i => F i (productCoordinateMix S x y i)) =
      productCoordinateMix S (fun i => F i (x i)) (fun i => F i (y i)) := by
  funext i
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi]

theorem productConditionalMean_coordinate_transport (p : ∀ i, FiniteProbabilityWeights (X i))
    (q : ∀ i, FiniteProbabilityWeights (Y i)) (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (p i).mean (fun x => f (F i x)) = (q i).mean f)
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean p S (fun y => f (fun i => F i (y i))) x =
      productConditionalMean q S f (fun i => F i (x i)) := by
  simp only [productConditionalMean, productCoordinateMix_map]
  exact productMean_coordinate_transport p q F hF
    (fun y => f (productCoordinateMix S (fun i => F i (x i)) y))

theorem productANOVA_coordinate_transport (p : ∀ i, FiniteProbabilityWeights (X i))
    (q : ∀ i, FiniteProbabilityWeights (Y i)) (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (p i).mean (fun x => f (F i x)) = (q i).mean f)
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productANOVA p S (fun y => f (fun i => F i (y i))) x =
      productANOVA q S f (fun i => F i (x i)) := by
  simp only [productANOVA, productConditionalMean_coordinate_transport p q F hF]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CylinderJointMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_ANOVA_ne (S T : Finset ι) (hST : S ≠ T)
    (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVA μ S f) (productANOVA ν T g) = 0 := by
  have h := productANOVA_orthogonal (fun i => (c i).law) S T hST
    (fun z => f (fun i => (z i).1)) (fun z => g (fun i => (z i).2))
  simpa only [productCouplingPairing, productANOVA_coordinate_transport _ μ (fun _ => Prod.fst) (fun i => (c i).left_mean),
    productANOVA_coordinate_transport _ ν (fun _ => Prod.snd) (fun i => (c i).right_mean)] using h

theorem productCouplingPairing_truncation (D : Finset (Finset ι))
    (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ D f) (productANOVATruncation ν D g) =
      ∑ S ∈ D, productCouplingPairing c (productANOVA μ S f) (productANOVA ν S g) := by
  simp only [productCouplingPairing, productANOVATruncation, Finset.sum_mul,
    Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_eq_single S]
  · intro T _ hTS
    simpa only [productCouplingPairing] using productCouplingPairing_ANOVA_ne c T S hTS f g
  · exact fun hn => False.elim (hn hS)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductKernelPairing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productJoint_mean (μ : ∀ i, FiniteProbabilityWeights (X i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (F : (∀ i, X i) → (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => (μ i).joint (K i))).mean
      (fun z => F (fun i => (z i).1) (fun i => (z i).2)) =
      (FiniteProbabilityWeights.pi μ).mean
        (fun x => (FiniteProbabilityWeights.pi (fun i => K i (x i))).mean (F x)) := by
  calc
    _ = ∑ z : (∀ i, X i) × (∀ i, Y i),
        (∏ i, (μ i).weight (z.1 i)) * (∏ i, (K i (z.1 i)).weight (z.2 i)) * F z.1 z.2 := by
      apply Fintype.sum_equiv (productPairCoordinates X Y)
      intro z
      change (∏ i, (μ i).weight (z i).1 * (K i (z i).1).weight (z i).2) * _ = _
      rw [Finset.prod_mul_distrib]
      rfl
    _ = _ := by
      simp only [Fintype.sum_prod_type, FiniteProbabilityWeights.mean,
        FiniteProbabilityWeights.pi, Finset.mul_sum, mul_assoc]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVASectionNormalizedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ S (fun y => c * f y) x = c * productANOVA μ S f x := by
  simp only [productANOVA, productConditionalMean_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} (q : ι → ℕ) (I : Finset ι)
  (hpair : Pairwise (fun i j => (q i).Coprime (q j)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ : Type*} (q : ι → ℕ) (I : Finset ι)
  (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
  (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) (r : σ → ZMod m)

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

theorem residuePrimeCoordinateDensity_congr_on_box
    (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (a : I → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f g : (I → ℤ) → ℝ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    residuePrimeCoordinateDensity lo N M a hne q f =
      residuePrimeCoordinateDensity lo N M a hne q g := by
  have heq : (fun z : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a =>
      f (fun i => (z i).val)) = (fun z => g (fun i => (z i).val)) := by
    funext z
    apply hfg
    apply (mem_translatedIntegerBox lo N _).mpr
    intro i
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1
  unfold residuePrimeCoordinateDensity
  dsimp only
  rw [heq]

theorem residuePhysicalTruncation_congr_on_box
    (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (a : I → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f g : (I → ℤ) → ℝ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    residuePhysicalTruncation lo N M a hne q b f =
      residuePhysicalTruncation lo N M a hne q b g := by
  funext x
  unfold residuePhysicalTruncation
  rw [residuePrimeCoordinateDensity_congr_on_box lo N M a hne q f g hfg]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxControl
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem physicalBoxResidual_eq_sub (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (hf : ∀ x ∉ translatedIntegerBox lo N, f x = 0) (x : I → ℤ) :
    physicalBoxResidual lo N P hpos q b f x = f x - physicalBoxTruncation lo N P hpos q b f x := by
  by_cases hx : x ∈ translatedIntegerBox lo N
  · simp only [physicalBoxResidual, if_pos hx]
  · simp only [physicalBoxResidual, physicalBoxTruncation, if_neg hx, dif_neg hx, hf x hx, sub_zero]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteRetainedCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

theorem residuePhysicalTruncation_cap (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (a : I → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta b) (x : I → ℤ) :
    |residuePhysicalTruncation lo N M a hne q b f x| ≤ residueTruncationCap ι b eta := by
  let := hne
  let p := FiniteProbabilityWeights.uniform
    (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a)
  let F := fun z : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a =>
    primeCoordinateObservation q (fun i => (z i).val)
  let w := fun z : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a => f (fun i => (z i).val)
  have hw (z) : 0 ≤ w z ∧ w z ≤ 1 := by
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro i
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1
  have hcap (S : Finset ι) (hS : S ∈ lowDegreeCoordinateSets ι b) :
      |productANOVA (primeCoordinateReference (σ := I) q) S
        (residuePrimeCoordinateDensity lo N M a hne q f) (primeCoordinateObservation q x)| ≤
      (2 : ℝ) ^ b * (1 + eta) := by
    have h := observedProductDensity_component_cap (primeCoordinateReference (σ := I) q) p F
      (primeCoordinateReference_weight_pos q) w zero_le_one heta hw hclose S
      ((mem_lowDegreeCoordinateSets ι b S).mp hS) (primeCoordinateObservation q x)
    simpa only [mul_one, residuePrimeCoordinateDensity, p, F, w] using h
  unfold residuePhysicalTruncation productANOVATruncation
  calc
    _ ≤ ∑ S ∈ lowDegreeCoordinateSets ι b,
        |productANOVA (primeCoordinateReference (σ := I) q) S
          (residuePrimeCoordinateDensity lo N M a hne q f) (primeCoordinateObservation q x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ lowDegreeCoordinateSets ι b, (2 : ℝ) ^ b * (1 + eta) :=
      Finset.sum_le_sum hcap
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, residueTruncationCap]; ring

theorem physicalBoxTruncation_cap (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ∀ c : (∀ i, (P i).Label), ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c)
        q (fun _ => 1)) eta b) (x : I → ℤ) :
    |physicalBoxTruncation lo N P hpos q b f x| ≤ residueTruncationCap ι b eta := by
  by_cases hx : x ∈ translatedIntegerBox lo N
  · simp only [physicalBoxTruncation, dif_pos hx]
    apply residuePhysicalTruncation_cap _ _ _ _ _ q b f _ heta
      (hclose (physicalBoxCell lo N P ⟨x, hx⟩)) x
    intro z hz
    exact hf z (physicalBoxCell_subset lo N P hstep hpos _ hz)
  · simp only [physicalBoxTruncation, dif_neg hx, abs_zero]
    unfold residueTruncationCap
    positivity

theorem weighted_event_discard_error {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (bad : X → Prop) (v g : X → ℝ)
    (hv : ∀ x, 0 ≤ v x ∧ v x ≤ 1) {C beta : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x, bad x → |g x| ≤ C) (hbad : p.eventProbability bad ≤ beta) :
    |p.mean (fun x => v x * g x) - p.mean (fun x => if bad x then 0 else v x * g x)| ≤ C * beta := by
  have heq : p.mean (fun x => v x * g x) - p.mean (fun x => if bad x then 0 else v x * g x) =
      p.mean (fun x => if bad x then v x * g x else 0) := by
    rw [← p.mean_sub]
    congr 1
    funext x
    split_ifs <;> simp
  rw [heq]
  apply (p.abs_mean_le_mean_abs _).trans
  calc
    _ ≤ p.mean (fun x => C * (if bad x then 1 else 0)) := by
      apply p.mean_mono
      intro x
      by_cases hx : bad x
      · simp only [if_pos hx, abs_mul, abs_of_nonneg (hv x).1, mul_one]
        exact (mul_le_mul (hv x).2 (hg x hx) (abs_nonneg _) zero_le_one).trans_eq (one_mul C)
      · simp only [if_neg hx, abs_zero, mul_zero]
        rfl
    _ = C * p.eventProbability bad := p.mean_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbad hC

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem finite_mean_le_of_retained_cells {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (cell : X → A) (bad : X → Prop) (f : X → ℝ)
    (hsat : ∀ x y, cell x = cell y → (bad x ↔ bad y))
    {R C beta : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbad : p.eventProbability bad ≤ beta) (hcap : ∀ x, bad x → |f x| ≤ C)
    (hcell : ∀ x, ¬ bad x → finiteCellMean p cell f (cell x) ≤
      R * (finiteCellWeights p cell).weight (cell x)) :
    p.mean f ≤ R + C * beta := by
  let kept := fun x => if bad x then 0 else f x
  have hlocal (a : A) : finiteCellMean p cell kept a ≤ R * (finiteCellWeights p cell).weight a := by
    by_cases ha : ∃ x, cell x = a ∧ ¬ bad x
    · obtain ⟨x, hxa, hx⟩ := ha
      have he : finiteCellMean p cell kept a = finiteCellMean p cell f a := by
        unfold finiteCellMean
        congr 1
        funext y
        by_cases hy : cell y = a
        · have hn : ¬ bad y := fun h => hx ((hsat y x (hy.trans hxa.symm)).mp h)
          simp only [kept, if_pos hy, if_neg hn]
        · simp only [if_neg hy]
      rw [he, ← hxa]
      exact hcell x hx
    · have he : finiteCellMean p cell kept a = 0 := by
        unfold finiteCellMean
        have hp (x : X) : (if cell x = a then kept x else 0) = 0 := by
          by_cases hx : cell x = a
          · have hb : bad x := by by_contra hn; exact ha ⟨x, hx, hn⟩
            simp only [kept, if_pos hx, if_pos hb]
          · exact if_neg hx
        simp only [hp, p.mean_const]
      rw [he]
      exact mul_nonneg hR ((finiteCellWeights p cell).nonneg a)
  have hk : p.mean kept ≤ R := by
    rw [← finiteCellMean_sum p cell kept]
    calc
      _ ≤ ∑ a, R * (finiteCellWeights p cell).weight a := Finset.sum_le_sum (fun a _ => hlocal a)
      _ = R := by rw [← Finset.mul_sum, (finiteCellWeights p cell).total, mul_one]
  have he := weighted_event_discard_error p bad (fun _ => 1) f (fun _ => ⟨zero_le_one, le_rfl⟩)
    hC hcap hbad
  simp only [one_mul] at he
  have hu := (abs_le.mp he).2
  change p.mean f - p.mean kept ≤ C * beta at hu
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ObservedMarginalTesting
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i) (hμ : ∀ i x, 0 < (μ i).weight x)

include hμ

theorem observedProductDensity_test_error (S : Finset ι) (g : (∀ i, X i) → ℝ)
    {eta C : ℝ} (heta : 0 ≤ eta) (hg : ProductDependsOn S g)
    (hclose : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ S (observedProductDensity μ p F (fun _ => 1)) x - 1| ≤ eta)
    (hcap : ∀ x, |g x| ≤ C) :
    |p.mean (fun z => g (F z)) - (FiniteProbabilityWeights.pi μ).mean g| ≤ eta * C := by
  have h := productMarginal_test_error μ (observedProductDensity μ p F (fun _ => 1))
    g S heta hg hclose (fun x _ => hcap x)
  rw [observedProductDensity_test μ p F hμ] at h
  simpa only [one_mul] using h

theorem observedProductDensity_family_test_error (D : Finset (Finset ι))
    (g : Finset ι → (∀ i, X i) → ℝ) {b : ℕ} {eta C : ℝ} (heta : 0 ≤ eta)
    (hcard : ∀ S ∈ D, S.card ≤ b) (hg : ∀ S ∈ D, ProductDependsOn S (g S))
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) eta b)
    (hcap : ∀ S ∈ D, ∀ x, |g S x| ≤ C) :
    |p.mean (fun z => ∑ S ∈ D, g S (F z)) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => ∑ S ∈ D, g S x)| ≤
      eta * D.card * C := by
  simp only [FiniteProbabilityWeights.mean_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ S ∈ D, |p.mean (fun z => g S (F z)) - (FiniteProbabilityWeights.pi μ).mean (g S)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ D, eta * C := by
      apply Finset.sum_le_sum
      intro S hS
      exact observedProductDensity_test_error μ p F hμ S (g S) heta (hg S hS)
        (hclose S (hcard S hS)) (hcap S hS)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalZeroExtension
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem physical_truncation_restore_difference
    {X I ι : Type*} [Fintype X] [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
    (p : FiniteProbabilityWeights X) (location : X → I → ℤ) (w : X → ℝ)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (b : ℕ) (h g : (I → ℤ) → ℝ)
    (hh : ∀ x ∉ translatedIntegerBox lo N, h x = 0)
    (hg : ∀ x ∉ translatedIntegerBox lo N, g x = 0)
    {r epsilon R : ℝ} (hr : 0 ≤ r)
    (heh : |p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b h (location x))| ≤ epsilon)
    (heg : |p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b g (location x))| ≤ epsilon)
    (hlow : p.mean (fun x => w x *
      (physicalBoxTruncation lo N P hpos q b h (location x) -
        r * physicalBoxTruncation lo N P hpos q b g (location x))) ≤ R) :
    p.mean (fun x => w x * (h (location x) - r * g (location x))) ≤ R + (1 + r) * epsilon := by
  have hid : p.mean (fun x => w x * (h (location x) - r * g (location x))) =
      p.mean (fun x => w x * (physicalBoxTruncation lo N P hpos q b h (location x) -
        r * physicalBoxTruncation lo N P hpos q b g (location x))) +
      p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b h (location x)) -
      r * p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b g (location x)) := by
    rw [← p.mean_add, ← p.mean_const_mul, ← p.mean_sub]
    congr 1
    funext x
    rw [physicalBoxResidual_eq_sub lo N P hpos q b h hh,
      physicalBoxResidual_eq_sub lo N P hpos q b g hg]
    ring
  rw [hid]
  have hhup := (abs_le.mp heh).2
  have hglow := mul_le_mul_of_nonneg_left (abs_le.mp heg).1 hr
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem physicalBoxTruncation_congr_on_box
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f g : (I → ℤ) → ℝ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    physicalBoxTruncation lo N P hpos q b f = physicalBoxTruncation lo N P hpos q b g := by
  funext x
  unfold physicalBoxTruncation
  split_ifs with hx
  · exact congrFun (residuePhysicalTruncation_congr_on_box _ _ _ _ _ q b f g
      (fun z hz => hfg z (physicalBoxCell_subset lo N P hstep hpos _ hz))) x
  · rfl

theorem physicalBoxResidual_congr_on_box
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f g : (I → ℤ) → ℝ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    physicalBoxResidual lo N P hpos q b f = physicalBoxResidual lo N P hpos q b g := by
  funext x
  unfold physicalBoxResidual
  rw [physicalBoxTruncation_congr_on_box lo N P hstep hpos q b f g hfg]
  split_ifs with hx
  · rw [hfg x hx]
  · rfl

theorem physicalBoxTruncation_zeroExtend
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) :
    physicalBoxTruncation lo N P hpos q b (realZeroExtendFinset (translatedIntegerBox lo N) f) =
      physicalBoxTruncation lo N P hpos q b f :=
  physicalBoxTruncation_congr_on_box lo N P hstep hpos q b _ f
    (fun _ hx => realZeroExtendFinset_on _ f hx)

theorem physicalBoxResidual_zeroExtend
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) :
    physicalBoxResidual lo N P hpos q b (realZeroExtendFinset (translatedIntegerBox lo N) f) =
      physicalBoxResidual lo N P hpos q b f :=
  physicalBoxResidual_congr_on_box lo N P hstep hpos q b _ f
    (fun _ hx => realZeroExtendFinset_on _ f hx)

theorem physical_zero_extension_restore_difference
    {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (location : X → I → ℤ) (w : X → ℝ)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (h g : (I → ℤ) → ℝ)
    {r epsilon R : ℝ} (hr : 0 ≤ r)
    (heh : |p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b h (location x))| ≤ epsilon)
    (heg : |p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b g (location x))| ≤ epsilon)
    (hlow : p.mean (fun x => w x *
      (physicalBoxTruncation lo N P hpos q b h (location x) -
        r * physicalBoxTruncation lo N P hpos q b g (location x))) ≤ R) :
    p.mean (fun x => w x *
      (realZeroExtendFinset (translatedIntegerBox lo N) h (location x) -
        r * realZeroExtendFinset (translatedIntegerBox lo N) g (location x))) ≤ R + (1 + r) * epsilon := by
  apply physical_truncation_restore_difference p location w lo N P hpos q b _ _
    (fun _ hx => realZeroExtendFinset_off _ h hx)
    (fun _ hx => realZeroExtendFinset_off _ g hx) hr
  · simpa only [physicalBoxResidual_zeroExtend lo N P hstep hpos q b h] using heh
  · simpa only [physicalBoxResidual_zeroExtend lo N P hstep hpos q b g] using heg
  · simpa only [physicalBoxTruncation_zeroExtend lo N P hstep hpos q b h,
      physicalBoxTruncation_zeroExtend lo N P hstep hpos q b g] using hlow

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScaledConditionedComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productANOVATruncation_smul (μ : ∀ i, FiniteProbabilityWeights (X i))
    (D : Finset (Finset ι)) (a : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => a * f y) x = a * productANOVATruncation μ D f x := by
  simp only [productANOVATruncation, productANOVA_smul, Finset.mul_sum]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_smul (a b : ℝ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (fun x => a * w x) (fun y => b * f y) = a * b * productCouplingPairing c w f := by
  unfold productCouplingPairing
  rw [← FiniteProbabilityWeights.mean_const_mul]
  congr 1
  funext z
  ring

theorem productCouplingPairing_truncation_smul (D : Finset (Finset ι)) (a b : ℝ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ D (fun x => a * w x))
      (productANOVATruncation ν D (fun y => b * f y)) =
      a * b * productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f) := by
  simp only [show productANOVATruncation μ D (fun x => a * w x) =
      (fun x => a * productANOVATruncation μ D w x) from funext (productANOVATruncation_smul μ D a w),
    show productANOVATruncation ν D (fun y => b * f y) =
      (fun y => b * productANOVATruncation ν D f y) from funext (productANOVATruncation_smul ν D b f),
    productCouplingPairing_smul]

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productANOVA_add (μ : ∀ i, FiniteProbabilityWeights (X i)) (S : Finset ι)
    (f g : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ S (fun y => f y + g y) x = productANOVA μ S f x + productANOVA μ S g x := by
  simp only [productANOVA, productConditionalMean, FiniteProbabilityWeights.mean_add,
    mul_add, Finset.sum_add_distrib]

theorem productANOVATruncation_add (μ : ∀ i, FiniteProbabilityWeights (X i)) (D : Finset (Finset ι))
    (f g : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => f y + g y) x =
      productANOVATruncation μ D f x + productANOVATruncation μ D g x := by
  simp only [productANOVATruncation, productANOVA_add, Finset.sum_add_distrib]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productTruncatedPairing_add_right (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun x => f x + g x) =
      productTruncatedPairing c D w f + productTruncatedPairing c D w g := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_add,
    mul_add, FiniteProbabilityWeights.mean_add]

theorem productTruncatedPairing_smul (D : Finset (Finset ι)) (a b : ℝ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (fun x => a * w x) (fun y => b * f y) =
      a * b * productTruncatedPairing c D w f := productCouplingPairing_truncation_smul c D a b w f

theorem productTruncatedPairing_sub_smul_right (D : Finset (Finset ι)) (a : ℝ)
    (w : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun y => f y - a * g y) =
      productTruncatedPairing c D w f - a * productTruncatedPairing c D w g := by
  have he : (fun y => f y - a * g y) = (fun y => f y + (-a) * g y) := by funext y; ring
  have hs := productTruncatedPairing_smul c D 1 (-a) w g
  simp only [one_mul] at hs
  rw [he, productTruncatedPairing_add_right, hs]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

variable {Ω : Type*} [Fintype Ω] [∀ i, DecidableEq (X i)]

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X Y : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
    (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i)) (e : J ↪ I)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)

include baseX baseY

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CouplingOneSidedTruncation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_ANOVA_right (S : Finset ι)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c w (productANOVA ν S f) =
      productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f) := by
  have hw : w = fun x => ∑ T ∈ (Finset.univ : Finset ι).powerset, productANOVA μ T w x := by
    funext x
    rw [productANOVA_reconstruct, productConditionalMean_univ]
  calc
    _ = productCouplingPairing c
        (fun x => ∑ T ∈ (Finset.univ : Finset ι).powerset, productANOVA μ T w x)
        (productANOVA ν S f) := congrArg (fun u => productCouplingPairing c u (productANOVA ν S f)) hw
    _ = ∑ T ∈ (Finset.univ : Finset ι).powerset,
        productCouplingPairing c (productANOVA μ T w) (productANOVA ν S f) := by
      simp only [productCouplingPairing, Finset.sum_mul, FiniteProbabilityWeights.mean_sum]
    _ = _ := by
      apply Finset.sum_eq_single S
      · intro T _ hTS
        exact productCouplingPairing_ANOVA_ne c T S hTS w f
      · intro hS
        exact False.elim (hS (Finset.mem_powerset.mpr (Finset.subset_univ S)))

theorem productCouplingPairing_truncation_right (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c w (productANOVATruncation ν D f) =
      productTruncatedPairing c D w f := by
  rw [productTruncatedPairing, productCouplingPairing_truncation]
  change productCouplingPairing c w (fun y => ∑ S ∈ D, productANOVA ν S f y) = _
  simp only [productCouplingPairing, Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  apply Finset.sum_congr rfl
  intro S _
  exact productCouplingPairing_ANOVA_right c S w f

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] {q : ℕ} [NeZero q]

theorem affinePeriodParameterLaw_mean (D : ℕ) (a : J → ℤ)
    (f : (J → ZMod q) → ℝ) :
    (affinePeriodParameterLaw D a).mean f =
      (FiniteProbabilityWeights.uniform (J → ZMod q)).mean
        (fun s => f (fun j => (a j : ZMod q) + (D : ZMod q) * s j)) :=
  FiniteProbabilityWeights.fiberLaw_mean _ _ _

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

variable [Fintype ι] [DecidableEq ι]

theorem affineParameterProductCoupling_pairing
    (π : ∀ i, FiniteProbabilityWeights (J → ZMod (q i)))
    (w : (∀ i, Option J × σ → ZMod (q i)) → ℝ)
    (f : (∀ i, σ → ZMod (q i)) → ℝ) :
    productCouplingPairing (affineParameterProductCoupling (σ := σ) q π) w f =
      (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := Option J × σ) q)).mean
        (fun z => w z * (FiniteProbabilityWeights.pi π).mean
          (fun t => f (fun i => (affineSampleAlphabetEquiv (z i)).2 +
            residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1 (t i)))) := by
  change (FiniteProbabilityWeights.pi (fun i =>
    (primeCoordinateReference (σ := Option J × σ) q i).joint (affineSampleParameterKernel (π i)))).mean
      (fun z => w (fun i => (z i).1) * f (fun i => (z i).2)) = _
  rw [productJoint_mean (primeCoordinateReference (σ := Option J × σ) q)
    (fun i => affineSampleParameterKernel (π i)) (fun x y => w x * f y)]
  simp only [FiniteProbabilityWeights.mean_const_mul]
  congr 1
  funext z
  congr 1
  exact (productMean_coordinate_transport π
    (fun i => affineSampleParameterKernel (π i) (z i))
    (fun i t => (affineSampleAlphabetEquiv (z i)).2 +
      residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1 t)
    (fun i g => (affineSampleParameterKernel_mean (π i) (z i) g).symm) f).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

variable [Fintype ι] [DecidableEq ι]

theorem affinePeriodProductCoupling_pairing (D : ℕ) (a : J → ℤ)
    (w : (∀ i, Option J × σ → ZMod (q i)) → ℝ)
    (f : (∀ i, σ → ZMod (q i)) → ℝ) :
    productCouplingPairing (affinePeriodProductCoupling (σ := σ) q D a) w f =
      (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := Option J × σ) q)).mean
        (fun z => w z * (FiniteProbabilityWeights.pi
          (fun i => FiniteProbabilityWeights.uniform (J → ZMod (q i)))).mean
          (fun s => f (fun i => (affineSampleAlphabetEquiv (z i)).2 +
            residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1
              (fun j => (a j : ZMod (q i)) + (D : ZMod (q i)) * s i j)))) := by
  rw [affinePeriodProductCoupling, affineParameterProductCoupling_pairing]
  congr 1
  funext z
  congr 1
  exact (productMean_coordinate_transport
    (fun i => FiniteProbabilityWeights.uniform (J → ZMod (q i)))
    (fun i => affinePeriodParameterLaw (q := q i) D a)
    (fun i s j => (a j : ZMod (q i)) + (D : ZMod (q i)) * s j)
    (fun i g => (affinePeriodParameterLaw_mean D a g).symm) _).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype J] [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

omit [Fintype I] [∀ i, NeZero (q i)] in
theorem affinePeriodResidueSample_integer (D : ℕ) (a t : J → ℤ)
    (z : Option J × I → ℤ) :
    primeCoordinateObservation q (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) =
      affinePeriodResidueSample q D a (primeCoordinateObservation q z) (primeCoordinateObservation q t) := by
  funext i k
  simp [primeCoordinateObservation, smoothAffineSample, affinePeriodResidueSample,
    affineSampleAlphabetEquiv, residueColumnMap]
  rfl

omit [Fintype I] [∀ i, NeZero (q i)] in
theorem affinePeriodResidueSample_depends (D : ℕ) (a : J → ℤ)
    (z : ∀ i, Option J × I → ZMod (q i)) (S : Finset ι)
    (f : (∀ i, I → ZMod (q i)) → ℝ) (hf : ProductDependsOn S f) :
    ProductDependsOn S (fun s => f (affinePeriodResidueSample q D a z s)) := by
  intro s t hst
  apply hf
  intro i hi
  dsimp only [affinePeriodResidueSample]
  rw [hst i hi]

variable [Fintype ι] [DecidableEq ι]

theorem affinePeriodProductCoupling_observed {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, Option J × I → ZMod (q i))
    (D : ℕ) (a : J → ℤ) (w : Ω → ℝ) (f : (∀ i, I → ZMod (q i)) → ℝ) :
    productCouplingPairing (affinePeriodProductCoupling (σ := I) q D a)
      (observedProductDensity (primeCoordinateReference (σ := Option J × I) q) p F w) f =
      p.mean (fun z => w z * (FiniteProbabilityWeights.pi
        (primeCoordinateReference (σ := J) q)).mean
          (fun s => f (affinePeriodResidueSample q D a (F z) s))) := by
  rw [affinePeriodProductCoupling_pairing]
  exact observedProductDensity_test (primeCoordinateReference (σ := Option J × I) q) p F
    (primeCoordinateReference_weight_pos q) w _

theorem affinePeriodTruncatedPairing_observed {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, Option J × I → ZMod (q i))
    (D : ℕ) (a : J → ℤ) (supports : Finset (Finset ι))
    (w : Ω → ℝ) (f : (∀ i, I → ZMod (q i)) → ℝ) :
    productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) supports
      (observedProductDensity (primeCoordinateReference (σ := Option J × I) q) p F w) f =
      p.mean (fun z => w z * (FiniteProbabilityWeights.pi
        (primeCoordinateReference (σ := J) q)).mean
          (fun s => productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
            (affinePeriodResidueSample q D a (F z) s))) := by
  rw [← productCouplingPairing_truncation_right]
  exact affinePeriodProductCoupling_observed q p F D a w _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I Ω Θ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype J] [Fintype I] [Fintype Ω] [Fintype Θ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

theorem affinePeriodTruncatedPairing_comparison
    (p : FiniteProbabilityWeights Ω) (r : FiniteProbabilityWeights Θ)
    (F : Ω → ∀ i, Option J × I → ZMod (q i)) (G : Θ → ∀ i, J → ZMod (q i))
    (D : ℕ) (a : J → ℤ) (supports : Finset (Finset ι))
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (f : (∀ i, I → ZMod (q i)) → ℝ) {b : ℕ} {eta C : ℝ} (heta : 0 ≤ eta)
    (hcard : ∀ S ∈ supports, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (observedProductDensity (primeCoordinateReference (σ := J) q) r G (fun _ => 1)) eta b)
    (hcap : ∀ S ∈ supports, ∀ x, |productANOVA (primeCoordinateReference (σ := I) q) S f x| ≤ C) :
    |p.mean (fun z => w z * r.mean (fun t =>
        productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
          (affinePeriodResidueSample q D a (F z) (G t)))) -
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) supports
        (observedProductDensity (primeCoordinateReference (σ := Option J × I) q) p F w) f| ≤
      eta * supports.card * C := by
  rw [affinePeriodTruncatedPairing_observed, ← p.mean_sub]
  apply p.abs_mean_le_on_support
  intro z _
  have he := observedProductDensity_family_test_error (primeCoordinateReference (σ := J) q)
    r G (primeCoordinateReference_weight_pos q) supports
    (fun S s => productANOVA (primeCoordinateReference (σ := I) q) S f
      (affinePeriodResidueSample q D a (F z) s)) heta hcard
    (fun S _ => affinePeriodResidueSample_depends q D a (F z) S _
      (productANOVA_depends (primeCoordinateReference (σ := I) q) S f))
    hclose (fun S hS x => hcap S hS (affinePeriodResidueSample q D a (F z) x))
  change |r.mean (fun t => productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
      (affinePeriodResidueSample q D a (F z) (G t))) -
    (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := J) q)).mean
      (fun s => productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
        (affinePeriodResidueSample q D a (F z) s))| ≤ _ at he
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw z).1]
  exact (mul_le_mul (hw z).2 he (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem affinePeriodTruncation_sample_comparison
    (p : FiniteProbabilityWeights Ω) (r : FiniteProbabilityWeights Θ)
    (source : Ω → Option J × I → ℤ) (index : Θ → J → ℤ)
    (D : ℕ) (a : J → ℤ) (supports : Finset (Finset ι))
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (f : (∀ i, I → ZMod (q i)) → ℝ) {b : ℕ} {eta C : ℝ} (heta : 0 ≤ eta)
    (hcard : ∀ S ∈ supports, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (observedProductDensity (primeCoordinateReference (σ := J) q) r
        (fun t => primeCoordinateObservation q (index t)) (fun _ => 1)) eta b)
    (hcap : ∀ S ∈ supports, ∀ x, |productANOVA (primeCoordinateReference (σ := I) q) S f x| ≤ C) :
    |p.mean (fun z => w z * r.mean (fun t =>
        productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
          (primeCoordinateObservation q
            (smoothAffineSample (fun j => a j + (D : ℤ) * index t j) (source z))))) -
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) supports
        (observedProductDensity (primeCoordinateReference (σ := Option J × I) q) p
          (fun z => primeCoordinateObservation q (source z)) w) f| ≤
      eta * supports.card * C := by
  simp only [affinePeriodResidueSample_integer]
  exact affinePeriodTruncatedPairing_comparison q p r
    (fun z => primeCoordinateObservation q (source z))
    (fun t => primeCoordinateObservation q (index t)) D a supports w hw f heta hcard hclose hcap

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residuePrimeCoordinateDensity_component_cap {ι I : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (a : I → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta b)
    (S : Finset ι) (hS : S.card ≤ b) (x : ∀ i, I → ZMod (q i)) :
    |productANOVA (primeCoordinateReference (σ := I) q) S
      (residuePrimeCoordinateDensity lo N M a hne q f) x| ≤ (2 : ℝ) ^ b * (1 + eta) := by
  let := hne
  have hw (z : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a) :
      0 ≤ f (fun i => (z i).val) ∧ f (fun i => (z i).val) ≤ 1 := by
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro i
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1
  have h := observedProductDensity_component_cap (primeCoordinateReference (σ := I) q)
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation q (fun i => (z i).val))
    (primeCoordinateReference_weight_pos q) (fun z => f (fun i => (z i).val))
    zero_le_one heta hw hclose S hS x
  simpa only [mul_one, residuePrimeCoordinateDensity] using h

variable {ι J I : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]
  (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
  (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
    (fun _ => 1) (fun _ => 0)))
  (paramLo : J → ℤ) (paramN : J → ℕ)
  (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
    (fun _ => 1) (fun _ => 0)))
  (siteLo : I → ℤ) (siteN : I → ℕ)
  (siteHne : Nonempty (IntegerResidueBox siteLo (fun i => siteLo i + siteN i)
    (fun _ => 1) (fun _ => 0)))
  (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (f : (I → ℤ) → ℝ)

theorem residueAffineTruncation_comparison
    (hw : ∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ w z ∧ w z ≤ 1)
    (hf : ∀ z ∈ translatedIntegerBox siteLo siteN, 0 ≤ f z ∧ f z ≤ 1)
    {etaParam etaSite : ℝ} (hparam : 0 ≤ etaParam) (hsite : 0 ≤ etaSite)
    (hcloseParam : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (residuePrimeCoordinateDensity paramLo paramN 1 (fun _ => 0) paramHne q (fun _ => 1)) etaParam b)
    (hcloseSite : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity siteLo siteN 1 (fun _ => 0) siteHne q (fun _ => 1)) etaSite b) :
    residueAffineTruncationError q sourceLo sourceN sourceHne paramLo paramN
      siteLo siteN siteHne D a b w f ≤ etaParam * residueTruncationCap ι b etaSite := by
  let := sourceHne
  let := paramHne
  have hw' (z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0)) :
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1 := by
    apply hw
    apply (mem_translatedIntegerBox sourceLo sourceN _).mpr
    intro i
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1
  have h := affinePeriodTruncation_sample_comparison q
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0)))
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0)))
    (fun z i => (z i).val) (fun t j => (t j).val) D a (lowDegreeCoordinateSets ι b)
    (fun z => w (fun i => (z i).val)) hw'
    (residuePrimeCoordinateDensity siteLo siteN 1 (fun _ => 0) siteHne q f)
    hparam (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mp hS) hcloseParam
    (fun S hS x => residuePrimeCoordinateDensity_component_cap siteLo siteN 1 (fun _ => 0)
      siteHne q b f hf hsite hcloseSite S ((mem_lowDegreeCoordinateSets ι b S).mp hS) x)
  convert h using 1 <;>
    simp only [residueAffineTruncationError, residuePhysicalTruncation, residuePrimeCoordinateDensity,
      FiniteProbabilityWeights.uniform_mean, residueTruncationCap, mul_assoc]
  congr 1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I]

theorem physicalBoxTruncation_of_classify_some (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (c : ∀ i, (P i).Label) (hx : physicalBoxClassify lo N P x = some c) :
    physicalBoxTruncation lo N P hpos q b f x =
      residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x := by
  by_cases h : x ∈ translatedIntegerBox lo N
  · simp only [physicalBoxClassify, dif_pos h, Option.some.injEq] at hx
    simp only [physicalBoxTruncation, dif_pos h]
    rw [hx]
  · simp only [physicalBoxClassify, dif_neg h] at hx
    cases hx

theorem physicalBoxTruncation_of_classify_none (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (hx : physicalBoxClassify lo N P x = none) :
    physicalBoxTruncation lo N P hpos q b f x = 0 := by
  by_cases h : x ∈ translatedIntegerBox lo N
  · simp only [physicalBoxClassify, dif_pos h] at hx
    cases hx
  · simp only [physicalBoxTruncation, dif_neg h]

theorem retained_physical_truncation_crt {J : Type*} [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
    (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
      (fun _ => 1) (fun _ => 0)))
    (paramLo : J → ℤ) (paramN : J → ℕ)
    (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
      (fun _ => 1) (fun _ => 0)))
    (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (f : (I → ℤ) → ℝ)
    (hw : ∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ w z ∧ w z ≤ 1)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hretained : ∀ z ∈ translatedIntegerBox sourceLo sourceN,
      ∀ t ∈ translatedIntegerBox paramLo paramN,
        physicalBoxClassify lo N P (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) = some c)
    {etaParam etaSite : ℝ} (hparam : 0 ≤ etaParam) (hsite : 0 ≤ etaSite)
    (hcloseParam : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (residuePrimeCoordinateDensity paramLo paramN 1 (fun _ => 0) paramHne q (fun _ => 1)) etaParam b)
    (hcloseSite : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c)
        q (fun _ => 1)) etaSite b) :
    |(𝔼 z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0),
        w (fun i => (z i).val) *
          (𝔼 t : IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0),
            physicalBoxTruncation lo N P hpos q b f
              (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) -
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
        (residuePrimeCoordinateDensity sourceLo sourceN 1 (fun _ => 0) sourceHne q w)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q f)| ≤
      etaParam * residueTruncationCap ι b etaSite := by
  have he (z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0))
      (t : IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0)) :
      physicalBoxTruncation lo N P hpos q b f
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)) =
        residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)) := by
    apply physicalBoxTruncation_of_classify_some
    apply hretained
    · exact (mem_translatedIntegerBox _ _ _).mpr
        (fun i => Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1)
    · exact (mem_translatedIntegerBox _ _ _).mpr
        (fun j => Finset.mem_Ico.mp (Finset.mem_filter.mp (t j).property).1)
  simp_rw [he]
  exact residueAffineTruncation_comparison q sourceLo sourceN sourceHne paramLo paramN paramHne
    (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => (P i).length (c i))
    (physicalBoxCell_nonempty lo N P hpos c) D a b w f hw
    (fun x hx => hf x (physicalBoxCell_subset lo N P hstep hpos c hx))
    hparam hsite hcloseParam hcloseSite

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedPhysicalDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem weighted_double_expect_sub_smul {X T : Type*} [Fintype X] [Fintype T]
    (w : X → ℝ) (f g : X → T → ℝ) (r : ℝ) :
    (𝔼 x : X, w x * (𝔼 t : T, (f x t - r * g x t))) =
      (𝔼 x, w x * (𝔼 t, f x t)) - r * (𝔼 x, w x * (𝔼 t, g x t)) := by
  simp only [Finset.expect_sub_distrib, ← Finset.mul_expect, mul_sub]
  congr 1
  rw [Finset.mul_expect]
  congr 1
  funext x
  ring

theorem retained_physical_truncation_difference_le
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
    (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
      (fun _ => 1) (fun _ => 0)))
    (paramLo : J → ℤ) (paramN : J → ℕ)
    (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
      (fun _ => 1) (fun _ => 0)))
    (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (h g : (I → ℤ) → ℝ)
    (hw : ∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ w z ∧ w z ≤ 1)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (hretained : ∀ z ∈ translatedIntegerBox sourceLo sourceN,
      ∀ t ∈ translatedIntegerBox paramLo paramN,
        physicalBoxClassify lo N P (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) = some c)
    {etaParam etaSite r R : ℝ} (hparam : 0 ≤ etaParam) (hsite : 0 ≤ etaSite) (hr : 0 ≤ r)
    (hcloseParam : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (residuePrimeCoordinateDensity paramLo paramN 1 (fun _ => 0) paramHne q (fun _ => 1)) etaParam b)
    (hcloseSite : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c)
        q (fun _ => 1)) etaSite b)
    (hreference : productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a)
      (lowDegreeCoordinateSets ι b)
      (residuePrimeCoordinateDensity sourceLo sourceN 1 (fun _ => 0) sourceHne q w)
      (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q h x -
        r * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q g x) ≤ R) :
    (𝔼 z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0),
      w (fun i => (z i).val) *
        (𝔼 t : IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0),
          (physicalBoxTruncation lo N P hpos q b h
              (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
            r * physicalBoxTruncation lo N P hpos q b g
              (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val))))) ≤
      R + (1 + r) * etaParam * residueTruncationCap ι b etaSite := by
  have heh := retained_physical_truncation_crt lo N P hstep hpos c q
    sourceLo sourceN sourceHne paramLo paramN paramHne D a b w h hw hh hretained
    hparam hsite hcloseParam hcloseSite
  have heg := retained_physical_truncation_crt lo N P hstep hpos c q
    sourceLo sourceN sourceHne paramLo paramN paramHne D a b w g hw hg hretained
    hparam hsite hcloseParam hcloseSite
  rw [productTruncatedPairing_sub_smul_right] at hreference
  rw [weighted_double_expect_sub_smul]
  have hhup := (abs_le.mp heh).2
  have hglow := mul_le_mul_of_nonneg_left (abs_le.mp heg).1 hr
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ConcreteAffineMeshBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxUniformWeights_eq_uniform {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) [Nonempty (∀ i, Finset.Ico (lo i) (hi i))] :
    integerBoxUniformWeights lo hi hlen = FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i)) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro x
  change (∏ i, (Fintype.card (Finset.Ico (lo i) (hi i)) : ℝ)⁻¹) =
    (Fintype.card (∀ i, Finset.Ico (lo i) (hi i)) : ℝ)⁻¹
  rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

theorem integerBoxMesh_pair_cell_mean {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (lo hi : I → ℤ) [Nonempty (∀ i, Finset.Ico (lo i) (hi i))]
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hPstep : ∀ i c, (P i).step c = 1) (hPpos : ∀ i c, 0 < (P i).length c)
    (tlo thi : J → ℤ) [Nonempty (∀ j, Finset.Ico (tlo j) (thi j))]
    (T : ∀ j, FiniteProgressionPartition (thi j - tlo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (c : ∀ i, (P i).Label) (d : ∀ j, (T j).Label) (f : (I → ℤ) → (J → ℤ) → ℝ) :
    finiteCellMean ((FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (tlo j) (thi j))).prod
        (FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i))))
      (fun tx => (integerBoxMesh lo hi P tx.2, integerBoxMesh tlo thi T tx.1))
      (fun tx => f (fun i => (tx.2 i).val) (fun j => (tx.1 j).val)) (c,d) =
      (finiteCellWeights (FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i)))
        (integerBoxMesh lo hi P)).weight c *
      (finiteCellWeights (FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (tlo j) (thi j)))
        (integerBoxMesh tlo thi T)).weight d *
      (𝔼 z : IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i)) (fun _ => 1) (fun _ => 0),
        𝔼 t : IntegerResidueBox (fun j => intervalCellLower (tlo j) (T j) (d j))
          (fun j => intervalCellLower (tlo j) (T j) (d j) + (T j).length (d j)) (fun _ => 1) (fun _ => 0),
          f (fun i => (z i).val) (fun j => (t j).val)) := by
  rw [finiteCellMean_product_uniform (integerBoxMesh lo hi P) (integerBoxMesh tlo thi T)
    (fun z t => f (fun i => (z i).val) (fun j => (t j).val)) c d]
  congr 1
  apply Fintype.expect_equiv (integerBoxMeshCellEquiv lo hi P hPstep hPpos c) _ _
  intro z
  exact Fintype.expect_equiv (integerBoxMeshCellEquiv tlo thi T hTstep hTpos d) _ _ (fun _ => rfl)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxMesh_cell_realize {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) (z : I → ℤ)
    (hz : z ∈ translatedIntegerBox (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i))) :
    ∃ x : (∀ i, Finset.Ico (lo i) (hi i)), integerBoxMesh lo hi P x = c ∧
      (fun i => (x i).val) = z := by
  let y := physicalBoxUnitResidueEquiv
    (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => (P i).length (c i)) ⟨z,hz⟩
  let e := integerBoxMeshCellEquiv lo hi P hstep hpos c
  let x := e.symm y
  refine ⟨x.val, x.property, ?_⟩
  funext i
  have he := congrArg (fun u => (u i).val) (e.apply_symm_apply y)
  change (x.val i).val = z i at he
  exact he

theorem retained_integer_mesh_boxes_classify
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (sourceLo sourceHi : Option J × I → ℤ)
    (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat)
    (hSstep : ∀ i c, (S i).step c = 1) (hSpos : ∀ i c, 0 < (S i).length c)
    (paramLo paramHi : J → ℤ)
    (T : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (D : ℕ) (a : J → ℤ)
    (x : (∀ j, Finset.Ico (paramLo j) (paramHi j)) ×
      (∀ i, Finset.Ico (sourceLo i) (sourceHi i)))
    (hx : ¬ physicalMeshCrossing lo N P
      (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
      (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)) x) :
    ∀ z ∈ translatedIntegerBox
        (fun i => intervalCellLower (sourceLo i) (S i) (integerBoxMesh sourceLo sourceHi S x.2 i))
        (fun i => (S i).length (integerBoxMesh sourceLo sourceHi S x.2 i)),
      ∀ t ∈ translatedIntegerBox
        (fun j => intervalCellLower (paramLo j) (T j) (integerBoxMesh paramLo paramHi T x.1 j))
        (fun j => (T j).length (integerBoxMesh paramLo paramHi T x.1 j)),
        physicalBoxClassify lo N P (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) =
          physicalBoxClassify lo N P
            (smoothAffineSample (fun j => a j + (D : ℤ) * (x.1 j).val) (fun i => (x.2 i).val)) := by
  intro z hz t ht
  obtain ⟨zs, hzs, hzv⟩ := integerBoxMesh_cell_realize sourceLo sourceHi S hSstep hSpos _ z hz
  obtain ⟨ts, hts, htv⟩ := integerBoxMesh_cell_realize paramLo paramHi T hTstep hTpos _ t ht
  have he := retained_mesh_cell_constant lo N P
    (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
    (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))
    x hx (ts,zs) (Prod.ext hzs hts)
  have htj (j : J) : (ts j).val = t j := congrFun htv j
  simpa only [hzv, htj] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshScalarTail
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_mesh_truncation_bound
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hPstep : ∀ i c, (P i).step c = 1) (hPpos : ∀ i c, 0 < (P i).length c)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ i, sourceLo i < sourceHi i)
    (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat)
    (hSstep : ∀ i c, (S i).step c = 1) (hSpos : ∀ i c, 0 < (S i).length c)
    (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
    (T : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (D : ℕ) (a : J → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ)
    (w : (Option J × I → ℤ) → ℝ) (h g : (I → ℤ) → ℝ)
    (hw : ∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    {etaParam etaSite r R beta : ℝ} (hetaParam : 0 ≤ etaParam) (hetaSite : 0 ≤ etaSite)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hcloseParam : ∀ ct : (∀ j, (T j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) q)
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (T j) (ct j))
          (fun j => (T j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) T hTpos ct)
          q (fun _ => 1)) etaParam b)
    (hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) q)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          q (fun _ => 1)) etaSite b)
    (hreference : ∀ cs : (∀ i, (S i).Label), ∀ c : (∀ i, (P i).Label),
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
          (fun i => (S i).length (cs i)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs) q w)
        (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q h x -
          r * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q g x) ≤ R)
    (hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
        (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta) :
    ((integerBoxUniformWeights paramLo paramHi hparam).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) *
        (physicalBoxTruncation lo N P hPpos q b h
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)) -
          r * physicalBoxTruncation lo N P hPpos q b g
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))) ≤
      R + (1 + r) * (etaParam + beta) * residueTruncationCap ι b etaSite := by
  let : Nonempty (∀ i, Finset.Ico (sourceLo i) (sourceHi i)) :=
    ⟨fun i => ⟨sourceLo i, Finset.mem_Ico.mpr ⟨le_rfl, hsource i⟩⟩⟩
  let : Nonempty (∀ j, Finset.Ico (paramLo j) (paramHi j)) :=
    ⟨fun j => ⟨paramLo j, Finset.mem_Ico.mpr ⟨le_rfl, hparam j⟩⟩⟩
  let ps := FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (sourceLo i) (sourceHi i))
  let pt := FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (paramLo j) (paramHi j))
  let p := pt.prod ps
  let ms := integerBoxMesh sourceLo sourceHi S
  let mt := integerBoxMesh paramLo paramHi T
  let mesh := fun tz : (∀ j, Finset.Ico (paramLo j) (paramHi j)) ×
      (∀ i, Finset.Ico (sourceLo i) (sourceHi i)) => (ms tz.2, mt tz.1)
  let location := fun tz : (∀ j, Finset.Ico (paramLo j) (paramHi j)) ×
      (∀ i, Finset.Ico (sourceLo i) (sourceHi i)) =>
    smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)
  let bad := physicalMeshCrossing lo N P mesh location
  let value := fun (z : Option J × I → ℤ) (t : J → ℤ) => w z *
    (physicalBoxTruncation lo N P hPpos q b h (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) -
      r * physicalBoxTruncation lo N P hPpos q b g (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z))
  let F := fun tz : (∀ j, Finset.Ico (paramLo j) (paramHi j)) ×
      (∀ i, Finset.Ico (sourceLo i) (sourceHi i)) => value (fun i => (tz.2 i).val) (fun j => (tz.1 j).val)
  let cap := residueTruncationCap ι b etaSite
  let K := R + (1 + r) * etaParam * cap
  have hcap0 : 0 ≤ cap := residueTruncationCap_nonneg ι b hetaSite
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hsLaw : integerBoxUniformWeights sourceLo sourceHi hsource = ps :=
    integerBoxUniformWeights_eq_uniform sourceLo sourceHi hsource
  have htLaw : integerBoxUniformWeights paramLo paramHi hparam = pt :=
    integerBoxUniformWeights_eq_uniform paramLo paramHi hparam
  rw [hsLaw, htLaw] at hbad ⊢
  change p.eventProbability bad ≤ beta at hbad
  change p.mean F ≤ R + (1 + r) * (etaParam + beta) * cap
  have hlocal (x) (hx : ¬ bad x) : finiteCellMean p mesh F (mesh x) ≤ K * (finiteCellWeights p mesh).weight (mesh x) := by
    let cs := ms x.2
    let ct := mt x.1
    have hclass := retained_integer_mesh_boxes_classify lo N P sourceLo sourceHi S hSstep hSpos
      paramLo paramHi T hTstep hTpos D a x hx
    have hwcell (z) (hz : z ∈ translatedIntegerBox
        (fun i => intervalCellLower (sourceLo i) (S i) (cs i)) (fun i => (S i).length (cs i))) :
        0 ≤ w z ∧ w z ≤ 1 := by
      obtain ⟨y, _, hy⟩ := integerBoxMesh_cell_realize sourceLo sourceHi S hSstep hSpos cs z hz
      simpa only [hy] using hw y
    have havg : (𝔼 z : IntegerResidueBox (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
        (fun i => intervalCellLower (sourceLo i) (S i) (cs i) + (S i).length (cs i)) (fun _ => 1) (fun _ => 0),
      𝔼 t : IntegerResidueBox (fun j => intervalCellLower (paramLo j) (T j) (ct j))
        (fun j => intervalCellLower (paramLo j) (T j) (ct j) + (T j).length (ct j)) (fun _ => 1) (fun _ => 0),
        value (fun i => (z i).val) (fun j => (t j).val)) ≤ K := by
      cases hc : physicalBoxClassify lo N P (location x) with
      | some c =>
          have ht := retained_physical_truncation_difference_le lo N P hPstep hPpos c q
            (fun i => intervalCellLower (sourceLo i) (S i) (cs i)) (fun i => (S i).length (cs i))
            (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs)
            (fun j => intervalCellLower (paramLo j) (T j) (ct j)) (fun j => (T j).length (ct j))
            (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) T hTpos ct)
            D a b w h g hwcell hh hg
            (fun z hz t ht => (hclass z hz t ht).trans hc) hetaParam hetaSite hr
            (hcloseParam ct) (hcloseSite c) (hreference cs c)
          simpa only [value, K, cap, ← Finset.mul_expect] using ht
      | none =>
          have he (z : IntegerResidueBox (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
              (fun i => intervalCellLower (sourceLo i) (S i) (cs i) + (S i).length (cs i)) (fun _ => 1) (fun _ => 0))
              (t : IntegerResidueBox (fun j => intervalCellLower (paramLo j) (T j) (ct j))
              (fun j => intervalCellLower (paramLo j) (T j) (ct j) + (T j).length (ct j)) (fun _ => 1) (fun _ => 0)) :
              value (fun i => (z i).val) (fun j => (t j).val) = 0 := by
            have hnone := (hclass (fun i => (z i).val)
              ((mem_translatedIntegerBox _ _ _).mpr (fun i => Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1))
              (fun j => (t j).val)
              ((mem_translatedIntegerBox _ _ _).mpr (fun j => Finset.mem_Ico.mp (Finset.mem_filter.mp (t j).property).1))).trans hc
            dsimp only [value]
            rw [physicalBoxTruncation_of_classify_none lo N P hPpos q b h _ hnone,
              physicalBoxTruncation_of_classify_none lo N P hPpos q b g _ hnone]
            ring
          simpa only [he, Finset.expect_const_zero] using hK
    have hm := integerBoxMesh_pair_cell_mean sourceLo sourceHi S hSstep hSpos
      paramLo paramHi T hTstep hTpos cs ct value
    have hwgt := finiteCellWeights_product ps pt ms mt cs ct
    change finiteCellMean p mesh F (cs,ct) ≤ K * (finiteCellWeights p mesh).weight (cs,ct)
    rw [hm, hwgt]
    exact (mul_le_mul_of_nonneg_left havg
      (mul_nonneg ((finiteCellWeights ps ms).nonneg cs) ((finiteCellWeights pt mt).nonneg ct))).trans_eq (mul_comm _ _)
  have hbound (x) (_ : bad x) : |F x| ≤ (1 + r) * cap := by
    have hhc := physicalBoxTruncation_cap lo N P hPstep hPpos q b h hh hetaSite hcloseSite (location x)
    have hgc := physicalBoxTruncation_cap lo N P hPstep hPpos q b g hg hetaSite hcloseSite (location x)
    have hd : |physicalBoxTruncation lo N P hPpos q b h (location x) -
        r * physicalBoxTruncation lo N P hPpos q b g (location x)| ≤ (1 + r) * cap := by
      apply (abs_sub _ _).trans
      rw [abs_mul, abs_of_nonneg hr]
      exact (add_le_add hhc (mul_le_mul_of_nonneg_left hgc hr)).trans_eq (by dsimp only [cap]; ring)
    change |w (fun i => (x.2 i).val) *
      (physicalBoxTruncation lo N P hPpos q b h (location x) -
        r * physicalBoxTruncation lo N P hPpos q b g (location x))| ≤ _
    rw [abs_mul, abs_of_nonneg (hw x.2).1]
    exact (mul_le_mul (hw x.2).2 hd (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hall := finite_mean_le_of_retained_cells p mesh bad F
    (fun x y hxy => physicalMeshCrossing_congr lo N P mesh location hxy)
    hK (by positivity : 0 ≤ (1 + r) * cap) hbad hbound hlocal
  exact hall.trans_eq (by dsimp only [K]; ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_mesh_zero_extension_bound
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hPstep : ∀ i c, (P i).step c = 1) (hPpos : ∀ i c, 0 < (P i).length c)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ i, sourceLo i < sourceHi i)
    (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat)
    (hSstep : ∀ i c, (S i).step c = 1) (hSpos : ∀ i c, 0 < (S i).length c)
    (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
    (T : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (D : ℕ) (a : J → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ)
    (w : (Option J × I → ℤ) → ℝ) (h g : (I → ℤ) → ℝ)
    (hw : ∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    {etaParam etaSite r R beta accuracy : ℝ} (hetaParam : 0 ≤ etaParam) (hetaSite : 0 ≤ etaSite)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hcloseParam : ∀ ct : (∀ j, (T j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) q)
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (T j) (ct j))
          (fun j => (T j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) T hTpos ct)
          q (fun _ => 1)) etaParam b)
    (hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) q)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          q (fun _ => 1)) etaSite b)
    (hreference : ∀ cs : (∀ i, (S i).Label), ∀ c : (∀ i, (P i).Label),
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
          (fun i => (S i).length (cs i)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs) q w)
        (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q h x -
          r * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q g x) ≤ R)
    (hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
        (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta)
    (heh : |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b h
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (heg : |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b g
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy) :
    ((integerBoxUniformWeights paramLo paramHi hparam).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) *
        (realZeroExtendFinset (translatedIntegerBox lo N) h
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)) -
          r * realZeroExtendFinset (translatedIntegerBox lo N) g
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))) ≤
      R + (1 + r) * ((etaParam + beta) * residueTruncationCap ι b etaSite + accuracy) := by
  have hlow := affine_mesh_truncation_bound lo N P hPstep hPpos
    sourceLo sourceHi hsource S hSstep hSpos paramLo paramHi hparam T hTstep hTpos
    D a q b w h g hw hh hg hetaParam hetaSite hr hR hcloseParam hcloseSite hreference hbad
  have hrestore := physical_zero_extension_restore_difference
    ((integerBoxUniformWeights paramLo paramHi hparam).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource))
    (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))
    (fun tz => w (fun i => (tz.2 i).val)) lo N P hPstep hPpos q b h g hr heh heg hlow
  exact hrestore.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_mesh_scalar_tail
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hPstep : ∀ i c, (P i).step c = 1) (hPpos : ∀ i c, 0 < (P i).length c)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ i, sourceLo i < sourceHi i)
    (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat)
    (hSstep : ∀ i c, (S i).step c = 1) (hSpos : ∀ i c, 0 < (S i).length c)
    (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
    (T : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (D : ℕ) (a : J → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ)
    (h g : (I → ℤ) → ℝ)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    {etaParam etaSite r R beta accuracy : ℝ} (hetaParam : 0 ≤ etaParam) (hetaSite : 0 ≤ etaSite)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hcloseParam : ∀ ct : (∀ j, (T j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) q)
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (T j) (ct j))
          (fun j => (T j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) T hTpos ct)
          q (fun _ => 1)) etaParam b)
    (hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) q)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          q (fun _ => 1)) etaSite b)
    (hreference : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      ∀ cs : (∀ i, (S i).Label), ∀ c : (∀ i, (P i).Label),
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
          (fun i => (S i).length (cs i)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs) q w)
        (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q h x -
          r * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q g x) ≤ R)
    (hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
        (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta)
    (heh : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b h
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (heg : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b g
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (p dominationLog : ℝ)
    (outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)))
    (hdom : ∀ z, outer.weight z ≤ Real.exp dominationLog *
      (integerBoxUniformWeights sourceLo sourceHi hsource).weight z)
    (herror : R + (1 + r) * ((etaParam + beta) * residueTruncationCap ι b etaSite + accuracy) ≤
      Real.exp (-(2 * p + dominationLog)) / 2) :
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights paramLo paramHi hparam).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) h
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        r * realZeroExtendFinset (translatedIntegerBox lo N) g
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤
      Real.exp (-p) := by
  apply fixedParameter_observed_tail_dominated
    (integerBoxUniformWeights sourceLo sourceHi hsource) outer
    (integerBoxUniformWeights paramLo paramHi hparam) (fun z i => (z i).val)
    (fun t z => realZeroExtendFinset (translatedIntegerBox lo N) h
        (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) z) -
      r * realZeroExtendFinset (translatedIntegerBox lo N) g
        (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) z)) p dominationLog hdom
  intro w hw
  exact (affine_mesh_zero_extension_bound lo N P hPstep hPpos sourceLo sourceHi hsource
    S hSstep hSpos paramLo paramHi hparam T hTstep hTpos D a q b w h g hw hh hg
    hetaParam hetaSite hr hR hcloseParam hcloseSite (hreference w hw) hbad
    (heh w hw) (heg w hw)).trans herror

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.affine_mesh_scalar_tail.{u_1, u_2, u_3} := @OAI.Erdos3.affine_mesh_scalar_tail.{u_1, u_2, u_3}
