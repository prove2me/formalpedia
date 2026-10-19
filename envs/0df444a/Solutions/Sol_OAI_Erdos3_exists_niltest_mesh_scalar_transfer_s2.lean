-- Prove2me | solution 1 for OAI.Erdos3.exists_niltest_mesh_scalar_transfer_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:15:08.396207+00:00
-- url     : https://prove2.me/submissions/0d7a928f-8791-42b7-be6c-92e15b82da26

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_affine_mesh_truncation_bound_s2
import Theorems.Thm_OAI_Erdos3_exists_baseline_comparison_tree_s2
import Theorems.Thm_OAI_Erdos3_global_cutoff_initial_atom_comparison_s2
import Theorems.Thm_OAI_Erdos3_unconditioned_affine_cell_bounds_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSliceCost
namespace OAI

section

namespace Erdos3

theorem PhysicalSubbox.length_le {σ : Type*} {parent lo : σ → ℤ} {H N : σ → ℕ}
    (h : PhysicalSubbox parent H lo N) (j : σ) : N j ≤ H j := by
  have hj := h j
  omega

end Erdos3

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

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

theorem finiteWeightDensity_mul (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (hsupport : ∀ x, p.weight x = 0 → w x = 0) (x : Ω) :
    p.weight x * finiteWeightDensity p w x = w x := by
  by_cases hx : p.weight x = 0
  · rw [hx, zero_mul, hsupport x hx]
  · unfold finiteWeightDensity
    field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem productFiberIndicator_depends {I : Type*} {X : I → Type*}
    (S : Finset I) (x : ∀ i, X i) : ProductDependsOn S (productFiberIndicator S x) := by
  intro y z hyz
  have he : (∀ i ∈ S, y i = x i) ↔ (∀ i ∈ S, z i = x i) :=
    ⟨fun h i hi => (hyz i hi).symm.trans (h i hi),
      fun h i hi => (hyz i hi).trans (h i hi)⟩
  simp only [productFiberIndicator, he]

theorem productFiberIndicator_self {I : Type*} {X : I → Type*}
    (S : Finset I) (x : ∀ i, X i) : productFiberIndicator S x x = 1 := by
  simp [productFiberIndicator]

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

theorem weight_le_productFiberMass (w : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (S : Finset I) (x : ∀ i, X i) : w x ≤ productFiberMass w S x := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun y => w y * productFiberIndicator S x y)
    (fun y _ => mul_nonneg (hw y) (by unfold productFiberIndicator; split_ifs <;> norm_num))
    (Finset.mem_univ x)
  simpa only [productFiberMass, productFiberIndicator_self, mul_one] using h

theorem productFiberMass_pos (p : FiniteProbabilityWeights (∀ i, X i))
    (S : Finset I) (x : ∀ i, X i) (hx : 0 < p.weight x) : 0 < productFiberMass p.weight S x :=
  hx.trans_le (weight_le_productFiberMass p.weight p.nonneg S x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_fiber_identity (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x * productConditionalMean μ S f x =
      productFiberMass (fun y => (FiniteProbabilityWeights.pi μ).weight y * f y) S x := by
  let p := FiniteProbabilityWeights.pi μ
  have he := productConditionalMean_selfadjoint μ S f (productFiberIndicator S x)
  simp_rw [productConditionalMean_of_depends μ S (productFiberIndicator_depends S x)] at he
  calc
    _ = p.mean (fun y => productConditionalMean μ S f y * productFiberIndicator S x y) := by
      unfold productFiberMass FiniteProbabilityWeights.mean
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      dsimp only
      by_cases hxy : ∀ i ∈ S, y i = x i
      · have hv := productConditionalMean_depends μ S f y x hxy
        rw [hv]
        dsimp [p]
        ring
      · simp only [productFiberIndicator, hxy, ite_false, mul_zero, zero_mul]
    _ = p.mean (fun y => f y * productFiberIndicator S x y) := he.symm
    _ = _ := by
      unfold productFiberMass FiniteProbabilityWeights.mean
      apply Finset.sum_congr rfl
      intro y _
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productFiberMass_fiberMean {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (f : Ω → ℝ)
    (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (fun y => p.fiberMean F y f) S x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) := by
  classical
  simp only [productFiberMass, FiniteProbabilityWeights.fiberMean, FiniteProbabilityWeights.mean,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [mul_ite, ite_mul, eq_comm, mul_assoc]

theorem observedProductDensity_fiber_identity {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (f : Ω → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x *
        productConditionalMean μ S (observedProductDensity μ p F f) x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) := by
  have hpos : ∀ y, 0 < (FiniteProbabilityWeights.pi μ).weight y :=
    fun y => Finset.prod_pos (fun i _ => hμ i (y i))
  rw [productConditionalMean_fiber_identity]
  have heq : (fun y => (FiniteProbabilityWeights.pi μ).weight y * observedProductDensity μ p F f y) =
      (fun y => p.fiberMean F y f) := by
    funext y
    exact finiteWeightDensity_mul _ _ (fun z hz => False.elim ((hpos z).ne' hz)) y
  rw [heq]
  exact productFiberMass_fiberMean p F f S x

theorem observedProductDensity_conditional {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (f : Ω → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ p F f) x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) /
        productFiberMass (FiniteProbabilityWeights.pi μ).weight S x := by
  have hp : 0 < (FiniteProbabilityWeights.pi μ).weight x :=
    Finset.prod_pos (fun i _ => hμ i (x i))
  apply (eq_div_iff (productFiberMass_pos _ S x hp).ne').mpr
  simpa only [mul_comm] using observedProductDensity_fiber_identity μ hμ p F f S x

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

variable [Fintype ι] [∀ i, Fintype (X i)]

theorem mem_bounded (b : ℕ) (c : ProductCylinder X) :
    c ∈ bounded (X := X) b ↔ c.1.card ≤ b := by
  classical
  simp only [bounded, Finset.mem_filter, Finset.mem_univ, true_and]

end ProductCylinder

end Erdos3

end

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

theorem bounded_card (b : ℕ) :
    (bounded (X := X) b).card =
      ∑ S ∈ lowDegreeCoordinateSets ι b, ∏ i : S, Fintype.card (X i.val) := by
  classical
  have he : bounded (X := X) b =
      (lowDegreeCoordinateSets ι b).sigma (fun S => (Finset.univ : Finset (∀ i : S, X i.val))) := by
    ext c
    simp only [mem_bounded, Finset.mem_sigma, mem_lowDegreeCoordinateSets, Finset.mem_univ, and_true]
  rw [he, Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_pi]

end Erdos3.ProductCylinder

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]

omit [Fintype ι] in
theorem productFiberIndicator_partition (I : Finset ι) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    (∑ a : ∀ i : I, X i, productFiberIndicator I (productSubtypePoint I a base) x * f x) = f x := by
  rw [← Finset.sum_mul, productFiberIndicator_sum_subtype, one_mul]

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

theorem productANOVA_sum (μ : ∀ i, FiniteProbabilityWeights (X i))
    {α : Type*} (s : Finset α) (f : α → (∀ i, X i) → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productANOVA μ S (fun y => ∑ a ∈ s, f a y) x = ∑ a ∈ s, productANOVA μ S (f a) x := by
  simp only [productANOVA, productConditionalMean, FiniteProbabilityWeights.mean_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem productANOVATruncation_sum (μ : ∀ i, FiniteProbabilityWeights (X i))
    {α : Type*} (s : Finset α) (f : α → (∀ i, X i) → ℝ) (D : Finset (Finset ι)) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => ∑ a ∈ s, f a y) x =
      ∑ a ∈ s, productANOVATruncation μ D (f a) x := by
  simp only [productANOVATruncation, productANOVA_sum]
  rw [Finset.sum_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productTruncatedPairing_sum_right {α : Type*} (s : Finset α) (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : α → (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun y => ∑ a ∈ s, f a y) =
      ∑ a ∈ s, productTruncatedPairing c D w (f a) := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_sum,
    Finset.mul_sum, FiniteProbabilityWeights.mean_sum]

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

theorem uniform_observedProductDensity_conditional {Ω ι : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (F : Ω → ∀ i, X i) (f : Ω → ℝ)
    (S : Finset ι) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ (FiniteProbabilityWeights.uniform Ω) F f) x =
      ((Fintype.card {z // ∀ i ∈ S, F z i = x i} : ℝ) / Fintype.card Ω /
        productFiberMass (FiniteProbabilityWeights.pi μ).weight S x) *
      (𝔼 z : {z // ∀ i ∈ S, F z i = x i}, f z.val) := by
  classical
  rw [observedProductDensity_conditional μ hμ]
  have hf : (fun z => f z * productFiberIndicator S x (F z)) =
      (fun z => if ∀ i ∈ S, F z i = x i then f z else 0) := by
    funext z
    unfold productFiberIndicator
    split_ifs <;> simp
  rw [hf, uniform_subtype_mean]
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy
namespace OAI

section

namespace Erdos3

theorem exp_neg_le_exp_neg_div_eight {A B : ℝ} (hAB : B + 4 ≤ A) :
    Real.exp (-A) ≤ Real.exp (-B) / 8 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 4 := by
    calc
      8 ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp (-(B + 4)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 4 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h8

theorem exp_neg_le_half_exp_neg {A B : ℝ} (hAB : B + 1 ≤ A) :
    Real.exp (-A) ≤ (1 / 2) * Real.exp (-B) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (-(B + 1)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 1 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-B) / 2 := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h2
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeTrace
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.trace_good {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (input : ∀ i, Value i) :
    Good (trace tree I x input).1 (trace tree I x input).2 := by
  induction h generalizing input with
  | leaf good => exact good
  | @split I x i children d fresh branches ih => exact ih (input i) input

theorem Valid.trace_card_le {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (input : ∀ i, Value i) :
    (trace tree I x input).1.card ≤ I.card + d := by
  induction h generalizing input with
  | leaf good => simp only [trace]; omega
  | @split I x i children d fresh branches ih =>
    have hchild := ih (input i) input
    have hcard := Finset.card_insert_of_notMem fresh
    change (trace (children (input i)) (insert i I) (Function.update x i (input i)) input).1.card ≤ _
    omega

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

theorem affineComparisonScale_bounds {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    0 ≤ affineComparisonScale ε L T C ∧
    L + T + 2 ≤ affineComparisonScale ε L T C ∧
    ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ) ≤ affineComparisonScale ε L T C ∧
    C ≤ affineComparisonScale ε L T C := by
  have hn : (0 : ℝ) ≤ (affineRemovalDepth T + affineComparisonTail ε L T : ℕ) := Nat.cast_nonneg _
  unfold affineComparisonScale
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem affineComparisonScale_count {ι : Type*} [Fintype ι] {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C) :
    (Fintype.card ι : ℝ) ≤ Real.exp (affineComparisonScale ε L T C) :=
  hcount.trans (Real.exp_le_exp.mpr (affineComparisonScale_bounds (ε := ε) hL hT hC).2.2.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedPrimePowers_pairwise_coprime {ι : Type*}
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime) :
    Pairwise (fun i j => (prime i ^ power i).Coprime (prime j ^ power j)) := by
  intro i j hij
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
  intro heq
  exact hij (hinj heq)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateReference_weight_pos {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (i : ι) (x : σ → ZMod (q i)) :
    0 < (primeCoordinateReference (σ := σ) q i).weight x := by
  dsimp only [primeCoordinateReference, FiniteProbabilityWeights.uniform]
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateDensity_conditional {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (residuePrimeCoordinateDensity lo N M a hne q f) x =
      residuePrimeCoordinateMassRatio lo N M a q I x *
        (𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)) := by
  let := hne
  exact uniform_observedProductDensity_conditional
    (Ω := IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a)
    (primeCoordinateReference (σ := σ) q)
    (primeCoordinateReference_weight_pos q)
    (fun z => primeCoordinateObservation q (fun j => (z j).val)) (fun z => f (fun j => (z j).val)) I x

theorem residuePrimeCoordinateDensity_conditional_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) x =
      residuePrimeCoordinateMassRatio lo N M a q I x := by
  classical
  rw [residuePrimeCoordinateDensity_conditional]
  by_cases hc : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)
  · let := hc
    rw [Fintype.expect_const, mul_one]
  · have hempty : IsEmpty (ResiduePrimeCoordinateCell lo N M a q I x) := not_nonempty_iff.mp hc
    let := hempty
    simp only [residuePrimeCoordinateMassRatio, Fintype.card_of_isEmpty, Nat.cast_zero,
      zero_div, zero_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

theorem residuePrimeCoordinateMassRatio_close_of_marginals {eta : ℝ} {A : ℕ}
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta A)
    (K : Finset ι) (hK : K.card ≤ A) (base : ∀ i, σ → ZMod (q i)) :
    |residuePrimeCoordinateMassRatio lo N M a q K base - 1| ≤ eta := by
  have h := hclose K hK base
    (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos q i (base i))).ne'
  rwa [residuePrimeCoordinateDensity_conditional_one] at h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeResidual
namespace OAI

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

theorem residueIndexLength_one_zero (a : ℤ) (N : ℕ) :
    residueIndexLength a (a + N) 1 0 = N := by
  rw [residueIndexLength_eq_card a (a + N) 1 0 (by norm_num)]
  simp [Int.modEq_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem partial_assignment_card_le_exp {ι : Type*} [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {V : ℝ} (hV : 0 ≤ V)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) (S : Finset ι) {j : ℕ} (hS : S.card ≤ j) :
    (Fintype.card (∀ i : S, X i.val) : ℝ) ≤ Real.exp ((j : ℝ) * V) := by
  classical
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ _i : S, Real.exp V := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hX i.val)
    _ = Real.exp ((S.card : ℝ) * V) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hV)

theorem ProductCylinder.bounded_card_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {P V : ℝ} (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) (j : ℕ) :
    ((ProductCylinder.bounded (X := X) j).card : ℝ) ≤ Real.exp ((j : ℝ) * (P + V + 1)) := by
  classical
  have he : ((ProductCylinder.bounded (X := X) j).card : ℝ) =
      ∑ S ∈ lowDegreeCoordinateSets ι j, (Fintype.card (∀ i : S, X i.val) : ℝ) := by
    simp only [ProductCylinder.bounded_card, Nat.cast_sum, Fintype.card_pi, Nat.cast_prod]
  rw [he]
  calc
    _ ≤ ∑ _S ∈ lowDegreeCoordinateSets ι j, Real.exp ((j : ℝ) * V) := by
      apply Finset.sum_le_sum
      intro S hS
      exact partial_assignment_card_le_exp hV hX S ((mem_lowDegreeCoordinateSets ι j S).mp hS)
    _ = ((lowDegreeCoordinateSets ι j).card : ℝ) * Real.exp ((j : ℝ) * V) := by simp
    _ ≤ Real.exp ((j : ℝ) * (P + 1)) * Real.exp ((j : ℝ) * V) :=
      mul_le_mul_of_nonneg_right (lowDegreeCoordinateSets_card_le_exp hP hcount j) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateLeafCount
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem trace_outside (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) (j : ι) (hj : j ∉ (trace tree I base input).1) :
    (trace tree I base input).2 j = base j := by
  induction tree generalizing I base with
  | leaf => rfl
  | split i children ih =>
    have hji : j ≠ i := by
      intro he
      subst j
      exact hj (trace_contains (children (input i)) (insert i I)
        (Function.update base i (input i)) input (Finset.mem_insert_self _ _))
    exact (ih (input i) (insert i I) (Function.update base i (input i)) hj).trans
      (Function.update_of_ne hji _ _)

theorem traceCylinder_assignment (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) :
    (traceCylinder tree I base input).assignment base = (trace tree I base input).2 := by
  funext i
  by_cases hi : i ∈ (trace tree I base input).1
  · exact ProductCylinder.assignment_mem _ base i hi
  · change (if h : i ∈ (trace tree I base input).1 then _ else base i) = _
    rw [dif_neg hi]
    exact (trace_outside tree I base input i hi).symm

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Value : ι → Type*}
  [∀ i, Fintype (Value i)]

theorem leafCylinders_partition (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) (f : (∀ i, Value i) → ℝ) (input : ∀ i, Value i) :
    (∑ c ∈ leafCylinders tree I base, productFiberIndicator c.1 (c.assignment base) input * f input) =
      productFiberIndicator I base input * f input := by
  rw [← Finset.sum_mul, leafCylinders_indicator_sum]

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}
  [∀ i, Fintype (Y i)]
  {Good : Finset ι → (∀ i, Y i) → Prop}
  {tree : CoordinateDecisionTree ι Y} {I : Finset ι} {base : ∀ i, Y i} {d : ℕ}

theorem Valid.leaf_good (h : Valid Good I base tree d)
    (c : ProductCylinder Y) (hc : c ∈ leafCylinders tree I base) :
    Good c.1 (c.assignment base) := by
  obtain ⟨input, _, rfl⟩ := (mem_leafCylinders tree I base c).mp hc
  rw [traceCylinder_assignment]
  exact h.trace_good input

theorem Valid.leaf_card_le (h : Valid Good I base tree d)
    (c : ProductCylinder Y) (hc : c ∈ leafCylinders tree I base) : c.1.card ≤ I.card + d := by
  obtain ⟨input, _, rfl⟩ := (mem_leafCylinders tree I base c).mp hc
  exact h.trace_card_le input

theorem Valid.leafCylinders_subset_bounded (h : Valid Good I base tree d)
    {A : ℕ} (hA : I.card + d ≤ A) :
    leafCylinders tree I base ⊆ ProductCylinder.bounded (X := Y) A := by
  intro c hc
  exact (ProductCylinder.mem_bounded A c).mpr ((h.leaf_card_le c hc).trans hA)

theorem Valid.leafCylinders_card_le_exp (h : Valid Good I base tree d)
    {A : ℕ} (hA : I.card + d ≤ A) {P W : ℝ} (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hY : ∀ i, (Fintype.card (Y i) : ℝ) ≤ Real.exp W) :
    ((leafCylinders tree I base).card : ℝ) ≤ Real.exp ((A : ℝ) * (P + W + 1)) :=
  (Nat.cast_le.mpr (Finset.card_le_card (h.leafCylinders_subset_bounded hA))).trans
    (ProductCylinder.bounded_card_le_exp hP hW hcount hY A)

theorem mem_leafSourceAssignments (X : ι → Type*) [∀ i, Fintype (X i)]
    (tree : CoordinateDecisionTree ι Y) (I : Finset ι) (base : ∀ i, Y i)
    (z : Σ c : ProductCylinder Y, ∀ i : c.1, X i.val) :
    z ∈ leafSourceAssignments X tree I base ↔ z.1 ∈ leafCylinders tree I base := by
  simp only [leafSourceAssignments, Finset.mem_sigma, Finset.mem_univ, and_true]

theorem Valid.leafSourceAssignments_card_le_exp (h : Valid Good I base tree d)
    (X : ι → Type*) [∀ i, Fintype (X i)] {A : ℕ} (hA : I.card + d ≤ A)
    {P V W : ℝ} (hP : 0 ≤ P) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V)
    (hY : ∀ i, (Fintype.card (Y i) : ℝ) ≤ Real.exp W) :
    ((leafSourceAssignments X tree I base).card : ℝ) ≤
      Real.exp ((A : ℝ) * (P + V + W + 1)) := by
  have hleaves := h.leafCylinders_card_le_exp hA hP hW hcount hY
  have hcard : ((leafSourceAssignments X tree I base).card : ℝ) =
      ∑ c ∈ leafCylinders tree I base, (Fintype.card (∀ i : c.1, X i.val) : ℝ) := by
    simp only [leafSourceAssignments, Finset.card_sigma, Finset.card_univ, Nat.cast_sum]
  rw [hcard]
  calc
    _ ≤ ∑ _c ∈ leafCylinders tree I base, Real.exp ((A : ℝ) * V) := by
      apply Finset.sum_le_sum
      intro c hc
      exact partial_assignment_card_le_exp hV hX c.1 ((h.leaf_card_le c hc).trans hA)
    _ = ((leafCylinders tree I base).card : ℝ) * Real.exp ((A : ℝ) * V) := by simp
    _ ≤ Real.exp ((A : ℝ) * (P + W + 1)) * Real.exp ((A : ℝ) * V) :=
      mul_le_mul_of_nonneg_right hleaves (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AdaptiveCouplingComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productTruncatedPairing_sum_left {α : Type*} (s : Finset α) (D : Finset (Finset ι))
    (w : α → (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (fun x => ∑ a ∈ s, w a x) f =
      ∑ a ∈ s, productTruncatedPairing c D (w a) f := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_sum,
    Finset.sum_mul, FiniteProbabilityWeights.mean_sum]

theorem productAtomTruncatedPairing_sum_source (D : Finset (Finset ι)) (I : Finset ι)
    (baseX : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    (∑ a : ∀ i : I, X i.val,
      productAtomTruncatedPairing c D I (productSubtypePoint I a baseX) y w f) =
      productTruncatedPairing c D w (fun z => productFiberIndicator I y z * f z) := by
  change (∑ a : ∀ i : I, X i.val,
    productTruncatedPairing c D (fun z => productFiberIndicator I (productSubtypePoint I a baseX) z * w z)
      (fun z => productFiberIndicator I y z * f z)) = _
  rw [← productTruncatedPairing_sum_left]
  have hw : (fun z => ∑ a : ∀ i : I, X i.val,
      productFiberIndicator I (productSubtypePoint I a baseX) z * w z) = w :=
    funext (fun z => productFiberIndicator_partition I baseX w z)
  rw [hw]

theorem productTruncatedPairing_leaf_partition (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (I : Finset ι) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun y => productFiberIndicator I baseY y * f y) =
      ∑ leaf ∈ CoordinateDecisionTree.leafCylinders tree I baseY,
        ∑ a : ∀ i : leaf.1, X i.val,
          productAtomTruncatedPairing c D leaf.1 (productSubtypePoint leaf.1 a baseX)
            (leaf.assignment baseY) w f := by
  symm
  simp_rw [productAtomTruncatedPairing_sum_source]
  rw [← productTruncatedPairing_sum_right]
  apply congrArg (productTruncatedPairing c D w)
  funext y
  exact CoordinateDecisionTree.leafCylinders_partition tree I baseY f y

theorem productTruncatedPairing_leaf_partition_empty (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w f =
      ∑ leaf ∈ CoordinateDecisionTree.leafCylinders tree ∅ baseY,
        ∑ a : ∀ i : leaf.1, X i.val,
          productAtomTruncatedPairing c D leaf.1 (productSubtypePoint leaf.1 a baseX)
            (leaf.assignment baseY) w f := by
  simpa [productFiberIndicator] using productTruncatedPairing_leaf_partition c tree D ∅ baseX baseY w f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem adaptiveLeafCouplingWeights_mean (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (F : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ) :
    (adaptiveLeafCouplingWeights c tree baseX baseY).mean (fun z => F z.val) =
      ∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
        adaptiveLeafPairMass c baseX baseY z * F z := by
  unfold FiniteProbabilityWeights.mean
  exact Finset.sum_coe_sort (CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY)
    (fun z => adaptiveLeafPairMass c baseX baseY z * F z)

theorem productTruncatedPairing_leaf_sigma (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w f =
      ∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
        productAtomTruncatedPairing c D z.1.1 (productSubtypePoint z.1.1 z.2 baseX)
          (z.1.assignment baseY) w f := by
  rw [CoordinateDecisionTree.leafSourceAssignments, Finset.sum_sigma]
  exact productTruncatedPairing_leaf_partition_empty c tree D baseX baseY w f

theorem productTruncatedPairing_leaf_bound (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (factor error : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ) (R : ℝ)
    (hbound : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      productAtomTruncatedPairing c D z.1.1 (productSubtypePoint z.1.1 z.2 baseX)
        (z.1.assignment baseY) w f ≤ adaptiveLeafPairMass c baseX baseY z * factor z * R + error z) :
    productTruncatedPairing c D w f ≤
      (adaptiveLeafCouplingWeights c tree baseX baseY).mean (fun z => factor z.val) * R +
        ∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, error z := by
  rw [productTruncatedPairing_leaf_sigma c tree D baseX baseY w f, adaptiveLeafCouplingWeights_mean]
  calc
    _ ≤ ∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
        (adaptiveLeafPairMass c baseX baseY z * factor z * R + error z) := Finset.sum_le_sum hbound
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptiveRatioNormalization
namespace OAI

section

namespace Erdos3

theorem abs_mul_sub_one_of_near_one {x y eta theta : ℝ}
    (hx : |x - 1| ≤ eta) (hy : |y - 1| ≤ theta) :
    |x * y - 1| ≤ eta + theta + eta * theta := by
  have heta : 0 ≤ eta := (abs_nonneg _).trans hx
  have habsy : |y| ≤ 1 + theta := by
    have h := abs_le.mp hy
    apply abs_le.mpr
    constructor <;> linarith
  calc
    |x * y - 1| = |(x - 1) * y + (y - 1)| := by congr 1; ring
    _ ≤ |(x - 1) * y| + |y - 1| := abs_add_le _ _
    _ = |x - 1| * |y| + |y - 1| := by rw [abs_mul]
    _ ≤ eta * (1 + theta) + theta :=
      add_le_add (mul_le_mul hx habsy (abs_nonneg _) heta) hy
    _ = _ := by ring

theorem FiniteProbabilityWeights.abs_mean_product_sub_one {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (x y : Ω → ℝ) {eta theta : ℝ}
    (hx : ∀ z, |x z - 1| ≤ eta) (hy : ∀ z, |y z - 1| ≤ theta) :
    |p.mean (fun z => x z * y z) - 1| ≤ eta + theta + eta * theta := by
  apply p.abs_mean_sub_const_le
  intro z
  exact abs_mul_sub_one_of_near_one (hx z) (hy z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem adaptive_ratio_product_close (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (sourceRatio siteRatio : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ)
    {eta theta : ℝ}
    (hs : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |sourceRatio z - 1| ≤ eta)
    (ht : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |siteRatio z - 1| ≤ theta) :
    |(adaptiveLeafCouplingWeights c tree baseX baseY).mean
      (fun z => sourceRatio z.val * siteRatio z.val) - 1| ≤ eta + theta + eta * theta :=
  FiniteProbabilityWeights.abs_mean_product_sub_one _ _ _
    (fun z => hs z.val z.property) (fun z => ht z.val z.property)

theorem adaptive_ratio_product_le (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (sourceRatio siteRatio : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ)
    {eta theta : ℝ}
    (hs : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |sourceRatio z - 1| ≤ eta)
    (ht : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |siteRatio z - 1| ≤ theta) :
    (adaptiveLeafCouplingWeights c tree baseX baseY).mean
      (fun z => sourceRatio z.val * siteRatio z.val) ≤ (1 + eta) * (1 + theta) := by
  have h := (abs_le.mp (adaptive_ratio_product_close c tree baseX baseY sourceRatio siteRatio hs ht)).2
  nlinarith only [h]

theorem productTruncatedPairing_leaf_normalized_bound (tree : CoordinateDecisionTree ι Y)
    (D : Finset (Finset ι)) (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (sourceRatio siteRatio error : (Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) → ℝ)
    {eta theta R E : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |sourceRatio z - 1| ≤ eta)
    (ht : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, |siteRatio z - 1| ≤ theta)
    (hbound : ∀ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      productAtomTruncatedPairing c D z.1.1 (productSubtypePoint z.1.1 z.2 baseX)
        (z.1.assignment baseY) w f ≤ adaptiveLeafPairMass c baseX baseY z *
          (sourceRatio z * siteRatio z) * R + error z)
    (herror : (∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY, error z) ≤ E) :
    productTruncatedPairing c D w f ≤ (1 + eta) * (1 + theta) * R + E := by
  have hraw := productTruncatedPairing_leaf_bound c tree D baseX baseY w f
    (fun z => sourceRatio z * siteRatio z) error R hbound
  have hn := mul_le_mul_of_nonneg_right
    (adaptive_ratio_product_le c tree baseX baseY sourceRatio siteRatio hs ht) hR
  exact hraw.trans (add_le_add hn herror)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCellLogCost
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*}

theorem physicalBoxCell_subbox (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (c : ∀ i, (P i).Label) :
    PhysicalSubbox lo N (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => (P i).length (c i)) := by
  intro i
  have hend : ((P i).start (c i) : ℤ) + (P i).length (c i) ≤ N i := by
    exact_mod_cast (P i).end_le_of_step_one (hstep i) (c i) (hpos i (c i))
  have hstart : (0 : ℤ) ≤ (P i).start (c i) := Int.natCast_nonneg _
  dsimp only [intervalCellLower]
  constructor <;> omega

theorem physicalBoxCell_log_cost (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (c : ∀ i, (P i).Label) (budget : ℝ)
    (hwidth : ∀ i, Real.exp (-budget) * (N i : ℝ) ≤ ((P i).length (c i) : ℝ)) :
    ResidueSliceLogCostLE N (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) budget := by
  intro i
  simpa only [Nat.cast_one, residueIndexLength_one_zero] using hwidth i

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem residue_function_alphabet_card_le_exp {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    {B : ℝ} (hq : (q : ℝ) ≤ Real.exp B) :
    (Fintype.card (I → ZMod q) : ℝ) ≤ Real.exp ((Fintype.card I : ℝ) * B) := by
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg q) hq _).trans_eq (Real.exp_nat_mul _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_leaf_source_assignments_card_le_exp {ι J σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    {Good : Finset ι → (∀ i, σ → ZMod (q i)) → Prop}
    {tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i))}
    {I : Finset ι} {base : ∀ i, σ → ZMod (q i)} {d A : ℕ}
    (h : CoordinateDecisionTree.Valid Good I base tree d) (hA : I.card + d ≤ A)
    {P modLog : ℝ} (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog) :
    ((CoordinateDecisionTree.leafSourceAssignments (fun i => Option J × σ → ZMod (q i)) tree I base).card : ℝ) ≤
      Real.exp ((A : ℝ) * (P + (Fintype.card (Option J × σ) : ℝ) * modLog +
        (Fintype.card σ : ℝ) * modLog + 1)) := by
  exact h.leafSourceAssignments_card_le_exp (fun i => Option J × σ → ZMod (q i)) hA hP
    (by positivity) (by positivity) hcount
    (fun i => by simpa only [Fintype.card_fun, ZMod.card] using
      residue_function_alphabet_card_le_exp (I := Option J × σ) (q := q i) (hmoduli i))
    (fun i => residue_function_alphabet_card_le_exp (I := σ) (q := q i) (hmoduli i))

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
  have hlow := affine_mesh_truncation_bound_s2 lo N P hPstep hPpos
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

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidueAccuracy
namespace OAI

section

namespace Erdos3

theorem affineComparisonAccuracy_bounds {P L T level : ℝ} (b : ℕ)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T) (hlevel : Real.exp (-L) ≤ level) :
    0 < affineComparisonAccuracy b P L T ∧ affineComparisonAccuracy b P L T < 1 ∧
    affineComparisonAccuracy b P L T ≤ Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ level * Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)) := by
  have hp : 0 ≤ (P + 3) ^ 3 := by positivity
  have hb : 0 ≤ 2 * (b : ℝ) * (P + 2) := by positivity
  have hpos : 0 < affineComparisonAccuracyLog b P L T := by
    unfold affineComparisonAccuracyLog
    linarith
  refine ⟨Real.exp_pos _, ?_, ?_, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.mpr (by linarith)
  · exact exp_neg_le_exp_neg_div_eight (by unfold affineComparisonAccuracyLog; linarith)
  · calc
      _ ≤ Real.exp (-(L + T)) / 8 :=
        exp_neg_le_exp_neg_div_eight (by unfold affineComparisonAccuracyLog; linarith)
      _ ≤ level * Real.exp (-T) / 8 := by
        rw [neg_add, Real.exp_add]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlevel (Real.exp_pos _).le) (by norm_num)
  · exact exp_neg_le_half_exp_neg (by unfold affineComparisonAccuracyLog; linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.InitialMaskedAffineComparison
namespace OAI

section

namespace Erdos3

theorem CyclicCrootSisask.spectralIterations_mono_budget {shell P Q : ℝ} (hPQ : P ≤ Q) :
    CyclicCrootSisask.spectralIterations shell P ≤ CyclicCrootSisask.spectralIterations shell Q := by
  unfold CyclicCrootSisask.spectralIterations
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrecisionBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalized_adaptive_affine_comparison
    {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
    {q : ι → ℕ} [∀ i, NeZero (q i)]
    (lo a : σ → ℤ) (N : σ → ℕ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (1 : ℤ)) a))
    (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ)
    (hneSource : Nonempty (IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
      (fun _ => (1 : ℤ)) sourceA))
    (h g : (σ → ℤ) → ℂ) (w : (Option J × σ → ℤ) → ℝ)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hw : ∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ w z ∧ w z ≤ 1)
    {ε L T C shell totalShell modLog level dimLog sourceDimLog : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hshell : 0 < shell) (hlower : Real.exp (-L) ≤ level) (hlevel2 : level ≤ 2)
    (hmodLog : 0 ≤ modLog) (hdimLog : 0 ≤ dimLog) (hsourceDimLog : 0 ≤ sourceDimLog)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
    (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hpower : ∀ i, q i = prime i ^ power i) (hinj : Function.Injective prime)
    (hJ : 2 ≤ Fintype.card J) (D : ℕ) (parameterA : J → ℤ)
    (tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i)))
    (baseX : ∀ i, Option J × σ → ZMod (q i)) (baseY : ∀ i, σ → ZMod (q i))
    {d A B : ℕ}
    (htree : CoordinateDecisionTree.Valid (fun K base =>
      affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D ⊆ K ∧
      ResiduePrimeCoordinateStable g lo N 1 a q (affineRemovalDepth T + affineComparisonTail ε L T)
        (affineStabilityTolerance T) K base ∧
      PrimeRefinementUpperBound h g lo N 1 a q (affineRemovalDepth T + affineComparisonTail ε L T)
        level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)
      ∅ baseY tree d)
    (hA : d ≤ A)
    (hB : A + affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ)
      ε L T C shell modLog ≤ B)
    (hBinitial : A + CyclicCrootSisask.spectralIterations shell
      ((A : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog +
        (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B)
    (hside : ∀ k, Real.exp (modLog * A + affineComparisonLengthLog B ε L T C modLog dimLog + 2) ≤ (N k : ℝ))
    (hsourceSide : ∀ k, Real.exp (modLog * A + affineComparisonLengthLog B ε L T C modLog sourceDimLog + 2) ≤ (sourceN k : ℝ))
    (hallocation : Real.exp ((A : ℝ) * (affineComparisonScale ε L T C +
      (Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1)) * shell ≤ totalShell) :
    productTruncatedPairing (affinePeriodProductCoupling (σ := σ) q D parameterA)
      (lowDegreeCoordinateSets ι B)
      (residuePrimeCoordinateDensity sourceLo sourceN 1 sourceA hneSource q w)
      (fun z => residuePrimeCoordinateDensity lo N 1 a hne q (fun x => (h x).re) z -
        (1 + ε) * level * residuePrimeCoordinateDensity lo N 1 a hne q (fun x => (g x).re) z) ≤
      (1 + affineComparisonAccuracy B (affineComparisonScale ε L T C) L T) *
      (1 + affineComparisonAccuracy B (affineComparisonScale ε L T C) L T) *
        (level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
          Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)) +
      (1 + (1 + ε) * level) * (totalShell / 16) := by
  have hpair : Pairwise (fun i k => (q i).Coprime (q k)) := by
    intro i k hik
    rw [hpower i, hpower k]
    exact selectedPrimePowers_pairwise_coprime prime power hprime hinj hik
  have hAB : A ≤ B := (Nat.le_add_right _ _).trans hB
  have hsite := unconditioned_affine_cell_bounds_s2 lo N a hne q hpair hAB hL hT hC
    hmodLog hdimLog hmoduli hdim hside
  have hsource := unconditioned_affine_cell_bounds_s2 sourceLo sourceN sourceA hneSource q hpair hAB
    hL hT hC hmodLog hsourceDimLog hmoduli hsourceDim hsourceSide
  let c := affinePeriodProductCoupling (σ := σ) q D parameterA
  let source := residuePrimeCoordinateDensity sourceLo sourceN 1 sourceA hneSource q w
  let target := fun z => residuePrimeCoordinateDensity lo N 1 a hne q (fun x => (h x).re) z -
    (1 + ε) * level * residuePrimeCoordinateDensity lo N 1 a hne q (fun x => (g x).re) z
  let eta := affineComparisonAccuracy B (affineComparisonScale ε L T C) L T
  let R := level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
    Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)
  let coeff := 1 + (1 + ε) * level
  let pairs := CoordinateDecisionTree.leafSourceAssignments (fun i => Option J × σ → ZMod (q i)) tree ∅ baseY
  let ratioX := fun z : Σ leaf : ProductCylinder (fun i => σ → ZMod (q i)),
      ∀ i : leaf.1, Option J × σ → ZMod (q i.val) =>
    residuePrimeCoordinateMassRatio sourceLo sourceN 1 sourceA q z.1.1 (productSubtypePoint z.1.1 z.2 baseX)
  let ratioY := fun z : Σ leaf : ProductCylinder (fun i => σ → ZMod (q i)),
      ∀ i : leaf.1, Option J × σ → ZMod (q i.val) =>
    residuePrimeCoordinateMassRatio lo N 1 a q z.1.1 (z.1.assignment baseY)
  have hA' : (∅ : Finset ι).card + d ≤ A := by simpa using hA
  have hleaf (z) (hz : z ∈ pairs) : z.1 ∈ CoordinateDecisionTree.leafCylinders tree ∅ baseY :=
    (CoordinateDecisionTree.mem_leafSourceAssignments (fun i => Option J × σ → ZMod (q i)) tree ∅ baseY z).mp hz
  have hsize (z) (hz : z ∈ pairs) : z.1.1.card ≤ A :=
    (htree.leaf_card_le z.1 (hleaf z hz)).trans hA'
  have hratioX (z) (hz : z ∈ pairs) : |ratioX z - 1| ≤ eta :=
    residuePrimeCoordinateMassRatio_close_of_marginals sourceLo sourceN 1 sourceA hneSource q
      hsource.1 z.1.1 (hsize z hz) (productSubtypePoint z.1.1 z.2 baseX)
  have hratioY (z) (hz : z ∈ pairs) : |ratioY z - 1| ≤ eta :=
    residuePrimeCoordinateMassRatio_close_of_marginals lo N 1 a hne q
      hsite.1 z.1.1 (hsize z hz) (z.1.assignment baseY)
  have hbound (z) (hz : z ∈ pairs) :
      productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) z.1.1
        (productSubtypePoint z.1.1 z.2 baseX) (z.1.assignment baseY) source target ≤
      adaptiveLeafPairMass c baseX baseY z * (ratioX z * ratioY z) * R + coeff * (shell / 16) := by
    have hcert := htree.leaf_good z.1 (hleaf z hz)
    let u := (hsite.2.1 z.1.1 (hsize z hz) (z.1.assignment baseY)).some
    let uX := (hsource.2.1 z.1.1 (hsize z hz) (productSubtypePoint z.1.1 z.2 baseX)).some
    have hwX (v : ResiduePrimeCoordinateCell sourceLo sourceN 1 sourceA q z.1.1
        (productSubtypePoint z.1.1 z.2 baseX)) :
        0 ≤ w (fun k => (v.val k).val) ∧ w (fun k => (v.val k).val) ≤ 1 := by
      apply hw
      apply (mem_translatedIntegerBox sourceLo sourceN _).mpr
      intro k
      exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (v.val k).property).1)
    have ha := global_cutoff_initial_atom_comparison_s2
      (hKcard := hsize z hz) (hB := hB) (hstable := hcert.2.1) (hupper := hcert.2.2)
      (hM := by decide) (u := u) (hg := hg) (hh := hh) (hL := hL) (hT := hT)
      (hlower := hlower) (prime := prime) (power := power) (hprime := hprime) (hpower := hpower)
      (hJ := hJ) (hshell := hshell) (hlevel2 := hlevel2) (hmodLog := hmodLog) (hmoduli := hmoduli)
      (hε := hε) (hC := hC) (hcount := hcount) (dimLog := dimLog) (hdim := hdim)
      (hlength := hsite.2.2 z.1.1 (hsize z hz) (z.1.assignment baseY) u)
      (sourceLo := sourceLo) (sourceA := sourceA) (sourceN := sourceN) (sourceM := 1)
      (sourceBase := productSubtypePoint z.1.1 z.2 baseX) (sourceCell := uX) (w := w) (hw := hwX)
      (hsourceM := by decide) (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim)
      (hsourceLength := hsource.2.2 z.1.1 (hsize z hz) (productSubtypePoint z.1.1 z.2 baseX) uX)
      (hinj := hinj) (D := D) (parameterA := parameterA) (hmask := hcert.1) (hBinitial := hBinitial)
    exact ha
  have hlevel : 0 ≤ level := (Real.exp_pos (-L)).le.trans hlower
  have hcoeff : 0 ≤ coeff := by dsimp only [coeff]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have hcountP := affineComparisonScale_count (ι := ι) (ε := ε) hL hT hC hcount
  have hcard := affine_leaf_source_assignments_card_le_exp (J := J) q htree hA' hP hmodLog hcountP hmoduli
  have herror : (∑ _z ∈ pairs, coeff * (shell / 16)) ≤ coeff * (totalShell / 16) := by
    have hpay := (mul_le_mul_of_nonneg_right hcard hshell.le).trans hallocation
    have hscale := mul_le_mul_of_nonneg_left hpay (div_nonneg hcoeff (by norm_num : (0 : ℝ) ≤ 16))
    calc
      _ = ((pairs.card : ℝ) * shell) * (coeff / 16) := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ totalShell * (coeff / 16) := by nlinarith only [hscale]
      _ = _ := by ring
  exact productTruncatedPairing_leaf_normalized_bound c tree (lowDegreeCoordinateSets ι B)
    baseX baseY source target ratioX ratioY (fun _ => coeff * (shell / 16)) hR hratioX hratioY hbound herror

end Erdos3

end

section

namespace Erdos3

theorem normalized_affine_error_le {ε T level eta shell totalShell : ℝ}
    (hε : 0 ≤ ε) (hT : 0 ≤ T) (hlevel : 0 ≤ level) (hlevel2 : level ≤ 2)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hshell : 0 ≤ shell) (htotal : shell ≤ totalShell) :
    (1 + eta) * (1 + eta) *
        (level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
          Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)) +
      (1 + (1 + ε) * level) * (totalShell / 16) ≤
    100 * (1 + ε) * Real.exp (-T / 2) + (1 + ε) * totalShell := by
  have he : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have he0 : 0 < Real.exp (-T) := Real.exp_pos _
  have htotal0 : 0 ≤ totalShell := hshell.trans htotal
  have hdecay : Real.exp (-T) ≤ Real.exp (-T / 2) := Real.exp_le_exp.mpr (by linarith)
  have hsquare : (Real.exp (-T / 2)) ^ 2 = Real.exp (-T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (3 * Real.exp (-T)) ≤ 2 * Real.exp (-T / 2) := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * Real.exp (-T / 2))).mpr
    nlinarith only [hsquare, he0]
  have hfirstCoeff : level * (1 + 2 * ε) ≤ 4 * (1 + ε) := by nlinarith
  have hfirst := mul_le_mul hfirstCoeff hdecay he0.le (by positivity : 0 ≤ 4 * (1 + ε))
  have htailCoeff : 3 + (1 + ε) * level * 3 ≤ 9 * (1 + ε) := by nlinarith
  have htail := mul_le_mul hsqrt htailCoeff
    (by positivity : 0 ≤ 3 + (1 + ε) * level * 3)
    (by positivity : 0 ≤ 2 * Real.exp (-T / 2))
  have hmain : level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
      Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3) ≤
      22 * (1 + ε) * Real.exp (-T / 2) + shell / 16 := by nlinarith only [hfirst, htail]
  have hmain0 : 0 ≤ level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
      Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3) := by positivity
  have hfactor : (1 + eta) * (1 + eta) ≤ 4 := by nlinarith
  have hcoeff : 1 + (1 + ε) * level ≤ 3 * (1 + ε) := by nlinarith
  have herr := mul_le_mul_of_nonneg_right hcoeff (div_nonneg htotal0 (by norm_num : (0 : ℝ) ≤ 16))
  have hrest : shell / 4 + 3 * (1 + ε) * (totalShell / 16) ≤ (1 + ε) * totalShell := by
    nlinarith only [htotal, htotal0, mul_nonneg hε htotal0]
  calc
    _ ≤ 4 * (level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
        Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)) +
        3 * (1 + ε) * (totalShell / 16) :=
      add_le_add (mul_le_mul_of_nonneg_right hfactor hmain0) herr
    _ ≤ 4 * (22 * (1 + ε) * Real.exp (-T / 2) + shell / 16) +
        3 * (1 + ε) * (totalShell / 16) := by
      linarith only [hmain]
    _ ≤ _ := by nlinarith only [hrest, mul_nonneg (by linarith : 0 ≤ 1 + ε) he.le]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GlobalAffineDegreeChoice
namespace OAI

section

namespace Erdos3

theorem affineGlobalComparisonDegree_bounds (A sourceDim siteDim : ℕ)
    (ε L T C shell modLog countLog : ℝ) (hcountLog : 0 ≤ countLog) :
    A + affineComparisonDegree sourceDim siteDim ε L T C shell modLog ≤
        affineGlobalComparisonDegree A sourceDim siteDim ε L T C shell modLog countLog ∧
    A + CyclicCrootSisask.spectralIterations shell
        ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4) ≤
        affineGlobalComparisonDegree A sourceDim siteDim ε L T C shell modLog countLog ∧
    A + CyclicCrootSisask.spectralIterations shell
        ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog) ≤
        affineGlobalComparisonDegree A sourceDim siteDim ε L T C shell modLog countLog := by
  have hm := CyclicCrootSisask.spectralIterations_mono_budget (shell := shell)
    (show (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 ≤
      (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog by linarith)
  unfold affineGlobalComparisonDegree
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeFamilyCutoff
namespace OAI

section

namespace Erdos3

theorem adaptiveAffineCountLog_nonneg (A sourceDim siteDim : ℕ)
    {ε L T C modLog : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmodLog : 0 ≤ modLog) :
    0 ≤ adaptiveAffineCountLog A sourceDim siteDim ε L T C modLog := by
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  unfold adaptiveAffineCountLog
  positivity

theorem adaptiveAffineShell_pos (A sourceDim siteDim : ℕ)
    (ε L T C modLog : ℝ) {totalShell : ℝ} (h : 0 < totalShell) :
    0 < adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog :=
  mul_pos h (Real.exp_pos _)

theorem adaptiveAffineShell_allocation (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) :
    Real.exp (adaptiveAffineCountLog A sourceDim siteDim ε L T C modLog) *
      adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog = totalShell := by
  unfold adaptiveAffineShell
  rw [mul_left_comm, ← Real.exp_add]
  simp

theorem adaptiveAffineShell_le (A sourceDim siteDim : ℕ)
    {ε L T C totalShell modLog : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hmodLog : 0 ≤ modLog) (h : 0 ≤ totalShell) :
    adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog ≤ totalShell := by
  have hexp := Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (adaptiveAffineCountLog_nonneg (ε := ε) A sourceDim siteDim hL hT hC hmodLog))
  exact (mul_le_mul_of_nonneg_left hexp h).trans_eq (mul_one totalShell)

theorem adaptiveAffineCutoff_bounds (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) :
    A + affineComparisonDegree sourceDim siteDim ε L T C
        (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog) modLog ≤
      adaptiveAffineCutoff A sourceDim siteDim ε L T C totalShell modLog ∧
    A + CyclicCrootSisask.spectralIterations
        (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog)
        ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4) ≤
      adaptiveAffineCutoff A sourceDim siteDim ε L T C totalShell modLog := by
  have h := affineGlobalComparisonDegree_bounds A sourceDim siteDim ε L T C
    (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog) modLog 0 le_rfl
  exact ⟨h.1, h.2.1⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestScalarTransfer
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_affine_reference_comparison (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype σ] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p ε L T C totalShell modLog dimLog sourceDimLog level : ℝ),
    2 ≤ p → 0 < ε → 0 ≤ L → 0 ≤ T → 0 ≤ C → 0 < totalShell →
    0 ≤ modLog → modLog ≤ p → 0 ≤ dimLog → 0 ≤ sourceDimLog → T + 4 ≤ p →
    Real.exp (-L) ≤ level → level ≤ 2 →
    (Fintype.card σ : ℝ) ≤ p → (Fintype.card ι : ℝ) ≤ Real.exp C →
    (Fintype.card σ : ℝ) ≤ Real.exp dimLog →
    (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : σ => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp modLog) →
    ∀ (D : ℕ) (parameterA : J → ℤ),
    ((affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D).card : ℝ) ≤ p →
    ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ) ≤ p →
    ∀ (parent lo a : σ → ℤ) (H N : σ → ℕ), PhysicalSubbox parent H lo N →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ResidueSliceLogCostLE H lo N 1 a p →
    ∀ (h : (σ → ℤ) → ℂ),
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval parent H ((p + 2) ^ E) level (affineIncrementTolerance L T) →
    ∀ (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (1 : ℤ)) a))
      (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ)
      (hneSource : Nonempty (IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
        (fun _ => (1 : ℤ)) sourceA)) (sourceWeight : (Option J × σ → ℤ) → ℝ),
    (∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ sourceWeight z ∧ sourceWeight z ≤ 1) →
    let A := ⌈(p + 2) ^ E⌉₊
    let B := adaptiveAffineCutoff A (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C totalShell modLog
    (∀ k, Real.exp (max ((p + 2) ^ E)
      (adaptiveAffineSideLog A (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C totalShell modLog dimLog)) ≤ (N k : ℝ)) →
    (∀ k, Real.exp (adaptiveAffineSideLog A (Fintype.card (Option J × σ)) (Fintype.card σ)
      ε L T C totalShell modLog sourceDimLog) ≤ (sourceN k : ℝ)) →
    productTruncatedPairing (affinePeriodProductCoupling (σ := σ) (fun i => prime i ^ power i) D parameterA)
      (lowDegreeCoordinateSets ι B)
      (residuePrimeCoordinateDensity sourceLo sourceN 1 sourceA hneSource (fun i => prime i ^ power i) sourceWeight)
      (fun z => residuePrimeCoordinateDensity lo N 1 a hne (fun i => prime i ^ power i) (fun x => (h x).re) z -
        (1 + ε) * level * residuePrimeCoordinateDensity lo N 1 a hne (fun i => prime i ^ power i) (fun x => (g.eval x).re) z) ≤
      100 * (1 + ε) * Real.exp (-T / 2) + (1 + ε) * totalShell := by
  obtain ⟨E, hE, htreeExists⟩ := exists_baseline_comparison_tree_s2.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ V J _ _ _ _ _ _ _ _ _ _ d nilmanifold p ε L T C totalShell modLog dimLog sourceDimLog level
    hp hε hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hσ hcount hdim hsourceDim hJ g hcomplexity prime power _ hprime hinj hmoduli
    D parameterA hmaskCard hr parent lo a H N hbox hunit hcost h hh hupper
    hne sourceLo sourceA sourceN hneSource sourceWeight hw A B hside hsourceSide
  let shell := adaptiveAffineShell A (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C totalShell modLog
  have hδ : 0 < affineStabilityTolerance T := Real.exp_pos _
  have hδinv : (affineStabilityTolerance T)⁻¹ ≤ Real.exp p := by
    simpa only [affineStabilityTolerance, Real.exp_neg, inv_inv] using Real.exp_le_exp.mpr hTP
  have hprimeP (i) : ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p :=
    (hmoduli i).trans (Real.exp_le_exp.mpr hmodLogP)
  have hlarge (k : σ) : Real.exp ((p + 2) ^ E) ≤ (H k : ℝ) :=
    ((Real.exp_le_exp.mpr (le_max_left _ _)).trans (hside k)).trans
      (by exact_mod_cast hbox.length_le k)
  have hlevel : 0 ≤ level := (Real.exp_pos (-L)).le.trans hlower
  obtain ⟨tree, depth, hdepth, htree⟩ := htreeExists nilmanifold p (affineStabilityTolerance T)
    hp hσ hδ hδinv g hcomplexity prime power hprime hinj hprimeP
    (affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D)
    (affineRemovalDepth T + affineComparisonTail ε L T) hmaskCard hr
    parent H N lo a 1 (by decide) hbox hunit hcost hlarge h level
    (affineIncrementTolerance L T) hlevel hupper
  have hA : depth ≤ A := by
    exact_mod_cast hdepth.trans (Nat.le_ceil ((p + 2) ^ E))
  have hB := adaptiveAffineCutoff_bounds A (Fintype.card (Option J × σ)) (Fintype.card σ)
    ε L T C totalShell modLog
  have hshell : 0 < shell := adaptiveAffineShell_pos A (Fintype.card (Option J × σ))
    (Fintype.card σ) ε L T C modLog htotal
  have hsideRaw (k : σ) :
      Real.exp (modLog * A + affineComparisonLengthLog B ε L T C modLog dimLog + 2) ≤ (N k : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hside k)
  have hallocation := (adaptiveAffineShell_allocation A (Fintype.card (Option J × σ))
    (Fintype.card σ) ε L T C totalShell modLog).le
  have hcomparison := normalized_adaptive_affine_comparison lo a N hne sourceLo sourceA sourceN hneSource
    h g.eval sourceWeight (fun z hz => (hunit z hz).2) hh hw hε hL hT hC hshell hlower hlevel2
    hmodLog hdimLog hsourceDimLog hmoduli hcount hdim hsourceDim prime power hprime (fun _ => rfl)
    hinj hJ D parameterA tree (fun _ _ => 0) (fun _ _ => 0) htree hA hB.1 hB.2 hsideRaw hsourceSide hallocation
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have heta := affineComparisonAccuracy_bounds (level := Real.exp (-L)) B hP hL hT le_rfl
  exact hcomparison.trans (normalized_affine_error_le hε.le hT hlevel hlevel2 heta.1.le heta.2.1.le
    hshell.le (adaptiveAffineShell_le A (Fintype.card (Option J × σ)) (Fintype.card σ) hL hT hC hmodLog htotal.le))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_mesh_reference_bounds (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {I : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype I] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p epsilon L T C totalShell modLog dimLog sourceDimLog level : ℝ),
    2 ≤ p → 0 < epsilon → 0 ≤ L → 0 ≤ T → 0 ≤ C → 0 < totalShell →
    0 ≤ modLog → modLog ≤ p → 0 ≤ dimLog → 0 ≤ sourceDimLog → T + 4 ≤ p →
    Real.exp (-L) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → (Fintype.card ι : ℝ) ≤ Real.exp C →
    (Fintype.card I : ℝ) ≤ Real.exp dimLog →
    (Fintype.card (Option J × I) : ℝ) ≤ Real.exp sourceDimLog → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp modLog) →
    ∀ (D : ℕ) (anchor : J → ℤ),
    ((affineSamplerPrimeMask prime (epsilon / (2 + epsilon)) (affineComparisonScale epsilon L T C) 1 1 D).card : ℝ) ≤ p →
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ p →
    ∀ (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)),
    (∀ i c, (P i).step c = 1) → ∀ (hPpos : ∀ i c, 0 < (P i).length c),
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    (∀ i c, Real.exp (-p) * (N i : ℝ) ≤ ((P i).length c : ℝ)) →
    ∀ (h : (I → ℤ) → ℂ),
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N ((p + 2) ^ E) level (affineIncrementTolerance L T) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ)
      (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat),
    (∀ i cs, (S i).step cs = 1) → ∀ (hSpos : ∀ i cs, 0 < (S i).length cs),
    ∀ sourceWeight : (Option J × I → ℤ) → ℝ,
    (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ sourceWeight (fun i => (z i).val) ∧ sourceWeight (fun i => (z i).val) ≤ 1) →
    let A := ⌈(p + 2) ^ E⌉₊
    let B := adaptiveAffineCutoff A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog
    (∀ i c, Real.exp (max ((p + 2) ^ E)
      (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
        epsilon L T C totalShell modLog dimLog)) ≤ ((P i).length c : ℝ)) →
    (∀ i cs, Real.exp (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog sourceDimLog) ≤ ((S i).length cs : ℝ)) →
    ∀ (cs : ∀ i, (S i).Label) (c : ∀ i, (P i).Label),
    productTruncatedPairing (affinePeriodProductCoupling (σ := I) (fun i => prime i ^ power i) D anchor)
      (lowDegreeCoordinateSets ι B)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
        (fun i => (S i).length (cs i)) 1 (fun _ => 0)
        (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs)
        (fun i => prime i ^ power i) sourceWeight)
      (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          (fun i => prime i ^ power i) (fun z => (h z).re) x -
        (1 + epsilon) * level * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          (fun i => prime i ^ power i) (fun z => (g.eval z).re) x) ≤
      100 * (1 + epsilon) * Real.exp (-T / 2) + (1 + epsilon) * totalShell := by
  obtain ⟨E, hE, href⟩ := exists_niltest_affine_reference_comparison.{u,v,w} s
  refine ⟨E, hE, ?_⟩
  intro ι I V J _ _ _ _ _ _ _ _ _ _ d nilmanifold p epsilon L T C totalShell modLog dimLog sourceDimLog level
    hp hepsilon hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hI hcount hdim hsourceDim hJ g hcomplexity prime power _ hprime hinj hmoduli
    D anchor hmask hdepth lo N P hPstep hPpos hunit hwidth h hh hupper
    sourceLo sourceHi S hSstep hSpos sourceWeight hw A B hside hsourceSide cs c
  have hsubset := physicalBoxCell_subset lo N P hPstep hPpos c
  have hwcell (z) (hz : z ∈ translatedIntegerBox
      (fun i => intervalCellLower (sourceLo i) (S i) (cs i)) (fun i => (S i).length (cs i))) :
      0 ≤ sourceWeight z ∧ sourceWeight z ≤ 1 := by
    obtain ⟨x, _, hx⟩ := integerBoxMesh_cell_realize sourceLo sourceHi S hSstep hSpos cs z hz
    simpa only [hx] using hw x
  exact href nilmanifold p epsilon L T C totalShell modLog dimLog sourceDimLog level
    hp hepsilon hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hI hcount hdim hsourceDim hJ g hcomplexity prime power hprime hinj hmoduli
    D anchor hmask hdepth lo (fun i => intervalCellLower (lo i) (P i) (c i)) (fun _ => 0)
    N (fun i => (P i).length (c i)) (physicalBoxCell_subbox lo N P hPstep hPpos c)
    (fun z hz => hunit z (hsubset hz)) (physicalBoxCell_log_cost lo N P c p (fun i => hwidth i (c i)))
    h (fun z hz => hh z (hsubset hz)) hupper (physicalBoxCell_nonempty lo N P hPpos c)
    (fun i => intervalCellLower (sourceLo i) (S i) (cs i)) (fun _ => 0) (fun i => (S i).length (cs i))
    (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs)
    sourceWeight hwcell (fun i => hside i (c i)) (fun i => hsourceSide i (cs i))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_mesh_scalar_transfer_s2_oai (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {I : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype I] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p epsilon L T C totalShell modLog dimLog sourceDimLog level : ℝ),
    2 ≤ p → 0 < epsilon → 0 ≤ L → 0 ≤ T → 0 ≤ C → 0 < totalShell →
    0 ≤ modLog → modLog ≤ p → 0 ≤ dimLog → 0 ≤ sourceDimLog → T + 4 ≤ p →
    Real.exp (-L) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → (Fintype.card ι : ℝ) ≤ Real.exp C →
    (Fintype.card I : ℝ) ≤ Real.exp dimLog →
    (Fintype.card (Option J × I) : ℝ) ≤ Real.exp sourceDimLog → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp modLog) →
    ∀ (D : ℕ) (anchor : J → ℤ),
    ((affineSamplerPrimeMask prime (epsilon / (2 + epsilon)) (affineComparisonScale epsilon L T C) 1 1 D).card : ℝ) ≤ p →
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ p →
    ∀ (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)),
    (∀ i c, (P i).step c = 1) → ∀ (hPpos : ∀ i c, 0 < (P i).length c),
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    (∀ i c, Real.exp (-p) * (N i : ℝ) ≤ ((P i).length c : ℝ)) →
    ∀ (h : (I → ℤ) → ℂ),
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N ((p + 2) ^ E) level (affineIncrementTolerance L T) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ)
      (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat),
    (∀ i cs, (S i).step cs = 1) → ∀ (_hSpos : ∀ i cs, 0 < (S i).length cs),
    ∀ (hsource : ∀ i, sourceLo i < sourceHi i),
    let A := ⌈(p + 2) ^ E⌉₊
    let B := adaptiveAffineCutoff A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog
    (∀ i c, Real.exp (max ((p + 2) ^ E)
      (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
        epsilon L T C totalShell modLog dimLog)) ≤ ((P i).length c : ℝ)) →
    (∀ i cs, Real.exp (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog sourceDimLog) ≤ ((S i).length cs : ℝ)) →
    ∀ (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
      (paramPartition : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat),
    (∀ j c, (paramPartition j).step c = 1) →
    ∀ (hTpos : ∀ j c, 0 < (paramPartition j).length c),
    ∀ (etaParam etaSite beta accuracy : ℝ), 0 ≤ etaParam → 0 ≤ etaSite →
    ∀ (_hcloseParam : ∀ ct : (∀ j, (paramPartition j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) (fun i => prime i ^ power i))
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (paramPartition j) (ct j))
          (fun j => (paramPartition j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) paramPartition hTpos ct)
          (fun i => prime i ^ power i) (fun _ => 1)) etaParam B)
    (_hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) (fun i => prime i ^ power i))
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          (fun i => prime i ^ power i) (fun _ => 1)) etaSite B)
    (_hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi paramPartition tz.1))
        (fun tz => smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta)
    (_heh : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos (fun i => prime i ^ power i) B (fun z => (h z).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (_heg : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos (fun i => prime i ^ power i) B (fun z => (g.eval z).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (pTarget dominationLog : ℝ)
    (outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)))
    (_hdom : ∀ z, outer.weight z ≤ Real.exp dominationLog *
      (integerBoxUniformWeights sourceLo sourceHi hsource).weight z)
    (_herror : (100 * (1 + epsilon) * Real.exp (-T / 2) + (1 + epsilon) * totalShell) + (1 + ((1 + epsilon) * level)) * ((etaParam + beta) * residueTruncationCap ι B etaSite + accuracy) ≤
      Real.exp (-(2 * pTarget + dominationLog)) / 2),
    outer.eventProbability (fun z => Real.exp (-pTarget) <
      (integerBoxUniformWeights paramLo paramHi hparam).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        ((1 + epsilon) * level) * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤
      Real.exp (-pTarget) := by
  obtain ⟨E, hE, href⟩ := exists_niltest_mesh_reference_bounds.{u,v,w} s
  refine ⟨E, hE, ?_⟩
  intro ι I V J _ _ _ _ _ _ _ _ _ _ d nilmanifold p epsilon L T C totalShell modLog dimLog sourceDimLog level
    hp hepsilon hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hI hcount hdim hsourceDim hJ g hcomplexity prime power _ hprime hinj hmoduli
    D anchor hmask hdepth lo N P hPstep hPpos hunit hwidth h hh hupper
    sourceLo sourceHi S hSstep hSpos hsource A B hside hsourceSide
    paramLo paramHi hparam paramPartition hTstep hTpos etaParam etaSite beta accuracy
    hetaParam hetaSite hcloseParam hcloseSite hbad heh heg pTarget dominationLog outer hdom herror
  apply affine_mesh_scalar_tail lo N P hPstep hPpos sourceLo sourceHi hsource
    S hSstep hSpos paramLo paramHi hparam paramPartition hTstep hTpos D anchor
    (fun i => prime i ^ power i) B (fun z => (h z).re) (fun z => (g.eval z).re)
    hh (fun z hz => (hunit z hz).2) hetaParam hetaSite
    (mul_nonneg (by linarith) ((Real.exp_pos (-L)).le.trans hlower))
    (by positivity) hcloseParam hcloseSite ?_ hbad heh heg pTarget dominationLog outer hdom herror
  intro sourceWeight hw cs c
  exact href nilmanifold p epsilon L T C totalShell modLog dimLog sourceDimLog level
    hp hepsilon hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hI hcount hdim hsourceDim hJ g hcomplexity prime power hprime hinj hmoduli
    D anchor hmask hdepth lo N P hPstep hPpos hunit hwidth h hh hupper
    sourceLo sourceHi S hSstep hSpos sourceWeight hw hside hsourceSide cs c

end Erdos3

end

end OAI
end

theorem solution.{u, v, w, u_1} : type_of% @OAI.Erdos3.exists_niltest_mesh_scalar_transfer_s2_oai.{u, v, w, u_1} := @OAI.Erdos3.exists_niltest_mesh_scalar_transfer_s2_oai.{u, v, w, u_1}
