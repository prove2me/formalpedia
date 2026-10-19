-- Prove2me | solution 1 for OAI.Erdos3.residuePhysicalTruncation_control_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:56:01.121986+00:00
-- url     : https://prove2.me/submissions/00d6bda8-6750-4860-825d-8769056a226e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

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

theorem productCoordinateMix_empty (x y : ∀ i, X i) :
    productCoordinateMix ∅ x y = y := by
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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem density_cauchy_schwarz (r f g : Ω → ℝ) (hr : ∀ x, 0 ≤ r x) :
    (p.mean (fun x => r x * f x * g x)) ^ 2 ≤
      p.mean (fun x => r x * f x ^ 2) * p.mean (fun x => r x * g x ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => mul_nonneg (p.nonneg x) (mul_nonneg (hr x) (sq_nonneg (f x))))
    (fun x _ => mul_nonneg (p.nonneg x) (mul_nonneg (hr x) (sq_nonneg (g x))))
  intro x _
  exact le_of_eq (by ring)

theorem density_square_le (r f : Ω → ℝ) (hr : ∀ x, 0 ≤ r x) {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    p.mean (fun x => r x * f x ^ 2) ≤ M * p.mean (fun x => r x * f x) := by
  rw [← p.mean_const_mul]
  apply p.mean_mono
  intro x
  have h := mul_le_mul_of_nonneg_left (hf x).2 (mul_nonneg (hr x) (hf x).1)
  nlinarith

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem ProductDependsOn.mul {I : Type*} [DecidableEq I] {X : I → Type*}
    {S T : Finset I} {f g : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (hg : ProductDependsOn T g) :
    ProductDependsOn (S ∪ T) (fun x => f x * g x) := by
  intro x y h
  change f x * g x = f y * g y
  rw [hf x y (fun i hi => h i (Finset.mem_union_left T hi)),
    hg x y (fun i hi => h i (Finset.mem_union_right S hi))]

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_empty (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ ∅ f x = (FiniteProbabilityWeights.pi μ).mean f := by
  simp only [productConditionalMean, productCoordinateMix_empty]

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

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem ProductMarginalsClose.mono {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s t : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (ht : t ≤ s) : ProductMarginalsClose μ rho eta t :=
  fun B hB x hx => h B (hB.trans ht) x hx

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

theorem productFamily_square_comparison (r : (∀ i, X i) → ℝ)
    (D : Finset (Finset I)) (u : Finset I → (∀ i, X i) → ℝ) {b : ℕ} {η C : ℝ}
    (hη : 0 ≤ η) (hC : 0 ≤ C) (hcard : ∀ S ∈ D, S.card ≤ b)
    (hdep : ∀ S ∈ D, ProductDependsOn S (u S))
    (hcap : ∀ S ∈ D, ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |u S x| ≤ C)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ S r x - 1| ≤ η) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * (∑ S ∈ D, u S x) ^ 2) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => (∑ S ∈ D, u S x) ^ 2)| ≤
        η * (D.card : ℝ) ^ 2 * C ^ 2 := by
  let p := FiniteProbabilityWeights.pi μ
  have hid : p.mean (fun x => r x * (∑ S ∈ D, u S x) ^ 2) -
      p.mean (fun x => (∑ S ∈ D, u S x) ^ 2) =
      ∑ S ∈ D, ∑ T ∈ D,
        (p.mean (fun x => r x * (u S x * u T x)) - p.mean (fun x => u S x * u T x)) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum,
      FiniteProbabilityWeights.mean_sum, Finset.sum_sub_distrib]
    simp only [mul_comm]
  rw [hid]
  calc
    _ ≤ ∑ S ∈ D, ∑ T ∈ D,
        |p.mean (fun x => r x * (u S x * u T x)) - p.mean (fun x => u S x * u T x)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun S _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _S ∈ D, ∑ _T ∈ D, η * C ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro T hT
      apply productMarginal_test_error μ r (fun x => u S x * u T x) (S ∪ T) hη
        ((hdep S hS).mul (hdep T hT))
      · apply hclose
        exact (Finset.card_union_le S T).trans (by have := hcard S hS; have := hcard T hT; omega)
      · intro x hx
        rw [abs_mul, pow_two]
        exact mul_le_mul (hcap S hS x hx) (hcap T hT x hx) (abs_nonneg _) hC
    _ = _ := by simp; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMarginal_l1_test_error (r g : (∀ i, X i) → ℝ) (S : Finset ι)
    {eta : ℝ} (hg : ProductDependsOn S g)
    (hr : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ S r x - 1| ≤ eta) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * g x) -
      (FiniteProbabilityWeights.pi μ).mean g| ≤
      eta * (FiniteProbabilityWeights.pi μ).mean (fun x => |g x|) := by
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
  apply (p.abs_mean_le_mean_abs _).trans
  rw [← p.mean_const_mul]
  apply p.mean_mono_on_support
  intro x hx
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hr x hx) (abs_nonneg _)

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

theorem productANOVA_pairing_self (S : Finset I) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x ^ 2) =
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productANOVA μ S f x) := by
  let p := FiniteProbabilityWeights.pi μ
  calc
    _ = p.mean (fun x => productANOVA μ S f x * productANOVA μ S f x) := by
      simp only [pow_two]
      rfl
    _ = ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
        p.mean (fun x => f x * productConditionalMean μ (S \ U) (productANOVA μ S f) x) := by
      change p.mean (fun x => (∑ U ∈ S.powerset,
        (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x) * productANOVA μ S f x) = _
      simp only [Finset.sum_mul, FiniteProbabilityWeights.mean_sum]
      apply Finset.sum_congr rfl
      intro U _
      calc
        _ = (-1 : ℝ) ^ U.card * p.mean (fun x =>
            productConditionalMean μ (S \ U) f x * productANOVA μ S f x) := by
          rw [← p.mean_const_mul]
          congr 1
          funext x
          ring
        _ = _ := by rw [← productConditionalMean_selfadjoint]
    _ = _ := by
      rw [Finset.sum_eq_single ∅]
      · simp only [Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty,
          productConditionalMean_ANOVA, Finset.Subset.refl, ite_true]
        rfl
      · intro U hU hUne
        have hUS := Finset.mem_powerset.mp hU
        have hn : ¬ S ⊆ S \ U := by
          obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hUne
          intro h
          exact (Finset.mem_sdiff.mp (h (hUS hi))).2 hi
        simp only [productConditionalMean_ANOVA, hn, ite_false, mul_zero, p.mean_const]
      · simp

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

theorem productANOVAEnergy_nonneg (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    0 ≤ productANOVAEnergy μ D f :=
  Finset.sum_nonneg (fun _ _ => (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => sq_nonneg _))

theorem productANOVAEnergy_pairing (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f =
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productANOVATruncation μ D f x) := by
  simp only [productANOVAEnergy, productANOVATruncation, Finset.mul_sum,
    FiniteProbabilityWeights.mean_sum, productANOVA_pairing_self]

theorem productANOVAEnergy_square (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVATruncation μ D f x ^ 2) =
      productANOVAEnergy μ D f := by
  simp only [productANOVATruncation, productANOVAEnergy, pow_two, Finset.sum_mul,
    Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_eq_single S]
  · intro T _ hTS
    exact productANOVA_orthogonal μ T S hTS f f
  · exact fun h => False.elim (h hS)

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_reconstruct (S : Finset ι) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    (∑ T ∈ S.powerset, productANOVA μ T f x) = productConditionalMean μ S f x :=
  subsetAlternatingTransform_sum S (fun T => productConditionalMean μ T f x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

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

theorem observedProductDensity_mean (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean (observedProductDensity μ p F f) = p.mean f := by
  have h := observedProductDensity_conditional μ hμ p F f ∅ base
  rw [productConditionalMean_empty, productFiberMass_empty, (FiniteProbabilityWeights.pi μ).total,
    div_one] at h
  simpa [productFiberIndicator] using h

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ObservedTruncationResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_truncation_eq (D : Finset (Finset ι)) (S : Finset ι)
    (hDS : ∀ T ⊆ S, T ∈ D) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ S (productANOVATruncation μ D f) x = productConditionalMean μ S f x := by
  have he : D.filter (fun T => T ⊆ S) = S.powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun hT => ⟨hDS T hT, hT⟩⟩
  change productConditionalMean μ S (fun y => ∑ T ∈ D, productANOVA μ T f y) x = _
  simp only [productConditionalMean_sum, productConditionalMean_ANOVA]
  rw [← Finset.sum_filter, he]
  exact productANOVA_reconstruct μ S f x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i) (hμ : ∀ i x, 0 < (μ i).weight x)
  (w : Ω → ℝ) (D : Finset (Finset ι))
  {b : ℕ} {eta C : ℝ} (heta : 0 ≤ eta) (hC : 0 ≤ C)
  (hcard : ∀ S ∈ D, S.card ≤ b)
  (hcap : ∀ S ∈ D, ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
    |productANOVA μ S (observedProductDensity μ p F w) x| ≤ C)
  (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) eta (2 * b))

include hμ heta hC hcard hcap hclose

theorem observed_truncation_square_error :
    |p.mean (fun z => (productANOVATruncation μ D (observedProductDensity μ p F w) (F z)) ^ 2) -
      productANOVAEnergy μ D (observedProductDensity μ p F w)| ≤ eta * (D.card : ℝ) ^ 2 * C ^ 2 := by
  have h := productFamily_square_comparison μ (observedProductDensity μ p F (fun _ => 1)) D
    (fun S => productANOVA μ S (observedProductDensity μ p F w)) heta hC hcard
    (fun S _ => productANOVA_depends μ S _) hcap hclose
  change |(FiniteProbabilityWeights.pi μ).mean (fun x => observedProductDensity μ p F (fun _ => 1) x *
      (productANOVATruncation μ D (observedProductDensity μ p F w) x) ^ 2) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => (productANOVATruncation μ D (observedProductDensity μ p F w) x) ^ 2)| ≤ _ at h
  rw [observedProductDensity_test μ p F hμ, productANOVAEnergy_square] at h
  simpa only [one_mul] using h

theorem observed_truncation_residual_square :
    p.mean (fun z => (w z - productANOVATruncation μ D (observedProductDensity μ p F w) (F z)) ^ 2) ≤
      p.mean (fun z => w z ^ 2) + eta * (D.card : ℝ) ^ 2 * C ^ 2 := by
  let f := observedProductDensity μ p F w
  let P := productANOVATruncation μ D f
  let E := productANOVAEnergy μ D f
  have he := observed_truncation_square_error μ p F hμ w D heta hC hcard hcap hclose
  have hp := observedProductDensity_test μ p F hμ w P
  rw [← productANOVAEnergy_pairing] at hp
  have hid : p.mean (fun z => (w z - P (F z)) ^ 2) =
      p.mean (fun z => w z ^ 2) - 2 * E + p.mean (fun z => P (F z) ^ 2) := by
    calc
      _ = p.mean (fun z => w z ^ 2 - 2 * (w z * P (F z)) + P (F z) ^ 2) := by
        congr 1
        funext z
        ring
      _ = _ := by rw [p.mean_add, p.mean_sub, p.mean_const_mul, ← hp]
  change p.mean (fun z => (w z - P (F z)) ^ 2) ≤ _
  rw [hid]
  have hE : 0 ≤ E := productANOVAEnergy_nonneg μ D f
  have hupper := (abs_le.mp he).2
  change p.mean (fun z => P (F z) ^ 2) - E ≤ _ at hupper
  linarith

omit hC in
theorem observed_truncation_local_test_error (I : Finset ι) (hI : I.card ≤ b)
    (hDI : ∀ S ⊆ I, S ∈ D) (a : (∀ i, X i) → ℝ) (ha : ProductDependsOn I a) :
    |p.mean (fun z => (w z - productANOVATruncation μ D (observedProductDensity μ p F w) (F z)) * a (F z))| ≤
      eta * D.card * C * (FiniteProbabilityWeights.pi μ).mean (fun x => |a x|) := by
  let ref := FiniteProbabilityWeights.pi μ
  let f := observedProductDensity μ p F w
  let rho := observedProductDensity μ p F (fun _ => 1)
  let P := productANOVATruncation μ D f
  have hterm (S) (hS : S ∈ D) :
      |ref.mean (fun x => rho x * (productANOVA μ S f x * a x)) -
        ref.mean (fun x => productANOVA μ S f x * a x)| ≤ eta * C * ref.mean (fun x => |a x|) := by
    have ht := productMarginal_l1_test_error μ rho (fun x => productANOVA μ S f x * a x) (S ∪ I)
      ((productANOVA_depends μ S f).mul ha)
      (hclose (S ∪ I) ((Finset.card_union_le S I).trans (by have := hcard S hS; omega)))
    have hl : ref.mean (fun x => |productANOVA μ S f x * a x|) ≤ C * ref.mean (fun x => |a x|) := by
      rw [← ref.mean_const_mul]
      apply ref.mean_mono_on_support
      intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcap S hS x hx) (abs_nonneg _)
    exact ht.trans ((mul_le_mul_of_nonneg_left hl heta).trans_eq (by ring))
  have hsum : |ref.mean (fun x => rho x * (P x * a x)) - ref.mean (fun x => P x * a x)| ≤
      eta * D.card * C * ref.mean (fun x => |a x|) := by
    have hid : ref.mean (fun x => rho x * (P x * a x)) - ref.mean (fun x => P x * a x) =
        ∑ S ∈ D, (ref.mean (fun x => rho x * (productANOVA μ S f x * a x)) -
          ref.mean (fun x => productANOVA μ S f x * a x)) := by
      simp only [P, productANOVATruncation, Finset.sum_mul, Finset.mul_sum,
        FiniteProbabilityWeights.mean_sum, Finset.sum_sub_distrib]
    rw [hid]
    calc
      _ ≤ ∑ S ∈ D, |ref.mean (fun x => rho x * (productANOVA μ S f x * a x)) -
          ref.mean (fun x => productANOVA μ S f x * a x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S ∈ D, eta * C * ref.mean (fun x => |a x|) := Finset.sum_le_sum hterm
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hcond := productConditionalMean_selfadjoint μ I f a
  have hcondP := productConditionalMean_selfadjoint μ I P a
  simp_rw [productConditionalMean_of_depends μ I ha] at hcond hcondP
  have hPeq : ∀ x, productConditionalMean μ I P x = productConditionalMean μ I f x :=
    productConditionalMean_truncation_eq μ D I hDI f
  simp_rw [hPeq] at hcondP
  have hcancel : p.mean (fun z => w z * a (F z)) = ref.mean (fun x => P x * a x) :=
    (observedProductDensity_test μ p F hμ w a).symm.trans (hcond.trans hcondP.symm)
  have hphysical := observedProductDensity_test μ p F hμ (fun _ => 1) (fun x => P x * a x)
  simp only [one_mul] at hphysical
  have hid : (fun z => (w z - P (F z)) * a (F z)) =
      (fun z => w z * a (F z) - P (F z) * a (F z)) := by funext z; ring
  change |p.mean (fun z => (w z - P (F z)) * a (F z))| ≤ _
  rw [hid, p.mean_sub, hcancel, ← hphysical, abs_sub_comm]
  exact hsum

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ObservedUnitTruncation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productTruncatedGram_bound (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M η : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset I)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ S r x - 1| ≤ η) :
    productANOVAEnergy μ D (fun x => r x * f x) ≤
      2 * M * (FiniteProbabilityWeights.pi μ).mean (fun x => r x * f x) +
        2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  let p := FiniteProbabilityWeights.pi μ
  let h := fun x => r x * f x
  let P := productANOVATruncation μ D h
  let A := productANOVAEnergy μ D h
  let B := M * p.mean h
  let C := (2 : ℝ) ^ b * M * (1 + η)
  let E := η * (D.card : ℝ) ^ 2 * C ^ 2
  have hM : 0 ≤ M := (p.mean_nonneg (fun x => (hf x).1)).trans
    ((p.mean_mono (fun x => (hf x).2)).trans_eq (p.mean_const M))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcap : ∀ S ∈ D, ∀ x, p.weight x ≠ 0 → |productANOVA μ S h x| ≤ C := by
    intro S hS x hx
    have hc := productANOVA_weighted_cap μ r f hr hM hf S
      (fun T hT => hclose T (by
        have := Finset.card_le_card hT
        have := hcard S hS
        omega)) x hx
    have hpw : (2 : ℝ) ^ S.card ≤ (2 : ℝ) ^ b := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) (hcard S hS)
    exact hc.trans (by
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_right hpw (mul_nonneg hM (by linarith : 0 ≤ 1 + η))])
  have herr := productFamily_square_comparison μ r D (fun S => productANOVA μ S h)
    hη hC hcard (fun S _ => productANOVA_depends μ S h) hcap hclose
  change |p.mean (fun x => r x * P x ^ 2) - p.mean (fun x => P x ^ 2)| ≤ E at herr
  have hsquare : p.mean (fun x => P x ^ 2) = A := productANOVAEnergy_square μ D h
  rw [hsquare] at herr
  have hpair : p.mean (fun x => r x * f x * P x) = A :=
    (productANOVAEnergy_pairing μ D h).symm
  have hA : 0 ≤ A := productANOVAEnergy_nonneg μ D h
  have hB : 0 ≤ B := mul_nonneg hM (p.mean_nonneg (fun x => mul_nonneg (hr x) (hf x).1))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hP : 0 ≤ p.mean (fun x => r x * P x ^ 2) :=
    p.mean_nonneg (fun x => mul_nonneg (hr x) (sq_nonneg _))
  have hquad : A ^ 2 ≤ B * (A + E) := by
    have hc := p.density_cauchy_schwarz r f P hr
    rw [hpair] at hc
    apply hc.trans
    apply mul_le_mul (p.density_square_le r f hr hf) _ hP hB
    have hh := (abs_le.mp herr).2
    linarith
  have hbound : A ≤ 2 * B + 2 * E := by
    by_contra hn
    have hpos : 0 < A := by linarith
    have h₁ := mul_nonneg (show 0 ≤ A - 2 * B by linarith) (show 0 ≤ A + E by linarith)
    have h₂ := mul_nonneg hpos.le (show 0 ≤ A - 2 * E by linarith)
    nlinarith [sq_pos_of_pos hpos]
  have htwo : ((2 : ℝ) ^ b) ^ 2 = (4 : ℝ) ^ b := by
    rw [← pow_mul, Nat.mul_comm b 2, pow_mul]
    norm_num
  have hEeq : E = η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
    dsimp [E, C]
    rw [mul_pow, mul_pow, htwo]
    ring
  calc
    _ ≤ 2 * B + 2 * E := hbound
    _ = _ := by rw [hEeq]; dsimp [B, h, p]; ring

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_truncatedGram_bound (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (w : Ω → ℝ) {M η : ℝ} (hM : 0 ≤ M)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b)) :
    productANOVAEnergy μ D (observedProductDensity μ p F w) ≤
      2 * M * p.mean w + 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w M hM hw
  have h := productTruncatedGram_bound μ (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (by intro z; norm_num)) hf hη D hcard hclose
  rw [← he, observedProductDensity_mean μ p F hμ w base] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem observed_unit_truncation_control {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (hμ : ∀ i x, 0 < (μ i).weight x) (base : ∀ i, X i)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (D : Finset (Finset ι))
    {b : ℕ} {eta : ℝ} (heta : 0 ≤ eta) (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) eta (2 * b)) :
    let P := productANOVATruncation μ D (observedProductDensity μ p F w)
    let cap := (D.card : ℝ) * (2 : ℝ) ^ b * (1 + eta)
    p.mean (fun z => P (F z) ^ 2) ≤ 2 + 3 * eta * cap ^ 2 ∧
    p.mean (fun z => (w z - P (F z)) ^ 2) ≤ 1 + eta * cap ^ 2 ∧
    ∀ (I : Finset ι), I.card ≤ b → (∀ S ⊆ I, S ∈ D) →
      ∀ a : (∀ i, X i) → ℝ, ProductDependsOn I a →
        |p.mean (fun z => (w z - P (F z)) * a (F z))| ≤
          eta * cap * (FiniteProbabilityWeights.pi μ).mean (fun x => |a x|) := by
  intro P cap
  let C := (2 : ℝ) ^ b * (1 + eta)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcap (S) (hS : S ∈ D) (x) (_hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
      |productANOVA μ S (observedProductDensity μ p F w) x| ≤ C := by
    have h := observedProductDensity_component_cap μ p F hμ w zero_le_one heta hw
      (ProductMarginalsClose.mono μ hclose (by omega : b ≤ 2 * b)) S (hcard S hS) x
    simpa only [mul_one] using h
  have hsquare := observed_truncation_square_error μ p F hμ w D heta hC hcard hcap hclose
  have hres := observed_truncation_residual_square μ p F hμ w D heta hC hcard hcap hclose
  have hgram := observedProductDensity_truncatedGram_bound μ p F hμ base w zero_le_one hw heta D hcard hclose
  norm_num only [one_pow, mul_one, mul_one] at hgram
  have hpow : ((2 : ℝ) ^ b) ^ 2 = (4 : ℝ) ^ b := by
    rw [← pow_mul, Nat.mul_comm b 2, pow_mul]
    norm_num
  have heq : eta * (D.card : ℝ) ^ 2 * C ^ 2 = eta * cap ^ 2 := by
    dsimp only [C, cap]
    ring
  have heqGram : 2 * eta * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + eta) ^ 2 = 2 * eta * cap ^ 2 := by
    dsimp only [cap]
    simp only [mul_pow, hpow]
    ring
  rw [heq] at hsquare hres
  rw [heqGram] at hgram
  have hwmean : p.mean w ≤ 1 := (p.mean_mono (fun z => (hw z).2)).trans_eq (p.mean_const 1)
  have hwsq : p.mean (fun z => w z ^ 2) ≤ 1 := by
    apply (p.mean_mono (g := fun _ => 1) ?_).trans_eq (p.mean_const 1)
    intro z
    have h := hw z
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have he := (abs_le.mp hsquare).2
    change p.mean (fun z => P (F z) ^ 2) ≤ _
    change p.mean (fun z => P (F z) ^ 2) - _ ≤ _ at he
    linarith
  · linarith
  · intro I hI hDI a ha
    have ht := observed_truncation_local_test_error μ p F hμ w D heta hcard hcap hclose I hI hDI a ha
    apply ht.trans_eq
    dsimp only [cap, C]
    ring

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

theorem residuePhysicalTruncation_control_s2_oai (b : ℕ) (f : (σ → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1) {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta (2 * b)) :
    ResiduePhysicalTruncationControl lo N M a hne q b f eta := by
  let := hne
  let p := FiniteProbabilityWeights.uniform
    (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a)
  let F := fun z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a =>
    primeCoordinateObservation q (fun k => (z k).val)
  let w := fun z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a =>
    f (fun k => (z k).val)
  have hw (z) : 0 ≤ w z ∧ w z ≤ 1 := by
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro k
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z k).property).1)
  have h := observed_unit_truncation_control (primeCoordinateReference (σ := σ) q) p F
    (primeCoordinateReference_weight_pos q) (fun _ _ => 0) w hw (lowDegreeCoordinateSets ι b)
    heta (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mp hS) hclose
  dsimp only [ResiduePhysicalTruncationControl]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [residuePhysicalTruncation, residueTruncationCap, residuePrimeCoordinateDensity,
      p, F, w, FiniteProbabilityWeights.uniform_mean] using h.1
  · simpa only [residuePhysicalTruncation, residueTruncationCap, residuePrimeCoordinateDensity,
      p, F, w, FiniteProbabilityWeights.uniform_mean] using h.2.1
  · intro I hI test htest
    have ht := h.2.2 I hI
      (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mpr ((Finset.card_le_card hS).trans hI)) test htest
    simpa only [residuePhysicalTruncation, residueTruncationCap, residuePrimeCoordinateDensity,
      p, F, w, FiniteProbabilityWeights.uniform_mean] using ht

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.residuePhysicalTruncation_control_s2_oai.{u_1, u_2} := @OAI.Erdos3.residuePhysicalTruncation_control_s2_oai.{u_1, u_2}
