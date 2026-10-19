-- Prove2me | solution 1 for OAI.Erdos3.residuePrimeCoordinateDensity_section_norm_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:56:01.949091+00:00
-- url     : https://prove2.me/submissions/2b84cb2b-983e-419f-8fe2-67e68a8ed445

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B197

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ObservedSourceEquivalence
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem uniform_observedProductDensity_source_equiv {Ω Ω' ι : Type*}
    [Fintype Ω] [Fintype Ω'] [Nonempty Ω] [Nonempty Ω'] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (e : Ω ≃ Ω')
    (F : Ω' → ∀ i, X i) (w : Ω' → ℝ) :
    observedProductDensity μ (FiniteProbabilityWeights.uniform Ω)
      (fun z => F (e z)) (fun z => w (e z)) =
      observedProductDensity μ (FiniteProbabilityWeights.uniform Ω') F w := by
  classical
  funext x
  unfold observedProductDensity finiteWeightDensity
  congr 1
  unfold FiniteProbabilityWeights.fiberMean
  dsimp only
  rw [FiniteProbabilityWeights.uniform_mean, FiniteProbabilityWeights.uniform_mean]
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

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

theorem productCoordinateMix_section (T A B : Finset I) (hAT : A ⊆ T)
    (z x y v : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y) =
      productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x)
        (productCoordinateMix Tᶜ y v) := by
  funext i
  by_cases hiT : i ∈ T
  · by_cases hiA : i ∈ A <;> simp [productCoordinateMix, hiT, hiA]
  · have hiA : i ∉ A := fun h => hiT (hAT h)
    by_cases hiB : i ∈ B <;> simp [productCoordinateMix, hiT, hiA, hiB]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_sectionAverage (T A B : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ B (productSectionAverage μ T A z f) x =
      productConditionalMean μ (A ∪ (B \ T)) f (productCoordinateMix T z x) := by
  change (FiniteProbabilityWeights.pi μ).mean (fun y => (FiniteProbabilityWeights.pi μ).mean
    (fun v => f (productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y)))) = _
  simp_rw [productCoordinateMix_section T A B hAT]
  exact productMean_coordinateMix μ Tᶜ
    (fun v => f (productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x) v))

theorem productSectionAverage_eq_conditionalMean (T A : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z f x =
      productConditionalMean μ (A ∪ Tᶜ) f (productCoordinateMix T z x) := by
  have h := productConditionalMean_sectionAverage μ T A Finset.univ hAT z f x
  have he : (Finset.univ \ T : Finset I) = Tᶜ := by ext i; simp
  simpa only [productConditionalMean_univ, he] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).mean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change (∏ i, (μ i).weight (x i)) * g (fun j => x (e j)) =
    (∏ j, (μ (e j)).weight (x (e j))) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem ProductDependsOn.subtypePoint {S : Finset I} {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (x base : ∀ i, X i) :
    f (productSubtypePoint S (fun i => x i) base) = f x := by
  apply hf
  intro i hi
  exact productSubtypePoint_apply_mem S (fun j => x j) base ⟨i, hi⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMean_restrict (S : Finset I) (g : (∀ i : S, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun i => x i)) =
      (FiniteProbabilityWeights.pi (fun i : S => μ i)).mean g := by
  classical
  let pS := FiniteProbabilityWeights.pi (fun i : S => μ i)
  let pC := FiniteProbabilityWeights.pi (fun i : {i // i ∉ S} => μ i)
  have hw (x : ∀ i, X i) : (FiniteProbabilityWeights.pi μ).weight x =
      pS.weight (fun i => x i) * pC.weight (fun i => x i) := by
    have hu : @Finset.univ S (Subtype.fintype (fun i : I => i ∈ S)) =
        @Finset.univ S (Finset.Subtype.fintype S) := by
      ext i
      simp only [Finset.mem_univ]
    simpa only [pS, pC, FiniteProbabilityWeights.pi, hu] using
      (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S) (fun i => (μ i).weight (x i))).symm
  calc
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun i => x i)) =
        ∑ z : (∀ i : S, X i) × (∀ i : {i // i ∉ S}, X i),
          pS.weight z.1 * pC.weight z.2 * g z.1 := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) X)
      intro x
      change (FiniteProbabilityWeights.pi μ).weight x * g (fun i => x i) =
        pS.weight (fun i => x i) * pC.weight (fun i => x i) * g (fun i => x i)
      rw [hw]
    _ = pS.mean g := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      calc
        (∑ v, pS.weight z * pC.weight v * g z) = pS.weight z * g z * ∑ v, pC.weight v := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          ring
        _ = pS.weight z * g z := by rw [pC.total, mul_one]

theorem productMean_of_depends (S : Finset I) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn S f) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean f =
      (FiniteProbabilityWeights.pi (fun i : S => μ i)).mean
        (fun z => f (productSubtypePoint S z base)) := by
  rw [← productMean_restrict μ S]
  congr 1
  funext x
  exact (hf.subtypePoint x base).symm

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

theorem productTuplePoint_apply (a : J → I) (ha : Function.Injective a)
    (v : ∀ j, X (a j)) (base : ∀ i, X i) (j : J) :
    productTuplePoint a ha v base (a j) = v j := by
  unfold productTuplePoint
  exact (productSubtypePoint_apply_mem (Finset.univ.image a) _ base
    (productTupleIndexEquiv a ha j)).trans
      (Equiv.piCongrLeft_apply_apply (fun i : ↥(Finset.univ.image a) => X i)
        (productTupleIndexEquiv a ha) v j)

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_tuple (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn (Finset.univ.image a) f) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi (fun j => μ (a j))).mean
      (fun v => f (productTuplePoint a ha v base)) = (FiniteProbabilityWeights.pi μ).mean f := by
  rw [productMean_of_depends μ (Finset.univ.image a) f hf base]
  let e := productTupleIndexEquiv a ha
  let eP := Equiv.piCongrLeft (fun i : ↥(Finset.univ.image a) => X i) e
  have h := productMean_reindex (fun i : ↥(Finset.univ.image a) => μ i) e
    (fun v => f (productTuplePoint a ha v base))
  have he (x : ∀ i : ↥(Finset.univ.image a), X i) :
      productTuplePoint a ha (fun j => x (e j)) base =
        productSubtypePoint (Finset.univ.image a) x base := by
    change productSubtypePoint (Finset.univ.image a) (eP (eP.symm x)) base = _
    rw [eP.apply_symm_apply]
  simp_rw [he] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_pullback (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (base : ∀ i, X i)
    (g : (∀ j, X (a j)) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun j => x (a j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (a j))).mean g := by
  have hd : ProductDependsOn (Finset.univ.image a) (fun x => g (fun j => x (a j))) := by
    intro x y h
    apply congrArg g
    funext j
    exact h (a j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have h := productMean_tuple μ a ha (fun x => g (fun j => x (a j))) hd base
  simpa only [productTuplePoint_apply] using h.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductReferenceFiber
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem productFiberMass_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x = ∏ i ∈ S, (μ i).weight (x i) := by
  classical
  have hind : ∀ y : ∀ i, X i, productFiberIndicator S x y =
      ∏ i, (if i ∈ S then if y i = x i then (1 : ℝ) else 0 else 1) := by
    intro y
    unfold productFiberIndicator
    split_ifs with h
    · symm
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i ∈ S
      · simp only [hi, h i hi, ite_true]
      · simp only [hi, ite_false]
    · push Not at h
      obtain ⟨i, hi, heq⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, heq, ite_true, ite_false]
  simp only [productFiberMass, hind, FiniteProbabilityWeights.pi, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (y : X i) => (μ i).weight y *
    (if i ∈ S then if y = x i then (1 : ℝ) else 0 else 1))]
  have hsum : ∀ i, (∑ y : X i, (μ i).weight y * (if i ∈ S then if y = x i then 1 else 0 else 1)) =
      if i ∈ S then (μ i).weight (x i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simpa only [hi, ite_false, mul_one] using (μ i).total
  simp only [hsum]
  rw [Finset.prod_ite]
  simp

theorem productFiberMass_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (X i))).weight S x =
      ∏ i ∈ S, (Fintype.card (X i) : ℝ)⁻¹ := by
  rw [productFiberMass_pi]
  rfl

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_conditional_commute (S T : Finset ι) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ S (productConditionalMean μ T f) x =
      productConditionalMean μ T (productANOVA μ S f) x := by
  change (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
      productConditionalMean μ (S \ U) (productConditionalMean μ T f) x) =
    productConditionalMean μ T (fun y => ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
      productConditionalMean μ (S \ U) f y) x
  simp only [productConditionalMean_sum, productConditionalMean_smul,
    productConditionalMean_comp, Finset.inter_comm]

theorem productANOVA_of_depends_not_subset (T : Finset ι) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn T f) (S : Finset ι) (hS : ¬S ⊆ T) (x : ∀ i, X i) :
    productANOVA μ S f x = 0 := by
  have he : productConditionalMean μ T f = f := funext (productConditionalMean_of_depends μ T hf)
  calc
    _ = productANOVA μ S (productConditionalMean μ T f) x := by rw [he]
    _ = productConditionalMean μ T (productANOVA μ S f) x := productANOVA_conditional_commute μ S T f x
    _ = 0 := by rw [productConditionalMean_ANOVA, if_neg hS]

theorem productANOVAEnergy_of_depends_filter (T : Finset ι) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn T f) (D : Finset (Finset ι)) :
    productANOVAEnergy μ D f = productANOVAEnergy μ (D.filter (fun S => S ⊆ T)) f := by
  classical
  unfold productANOVAEnergy
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ⊆ T
  · rw [if_pos hS]
  · simp only [if_neg hS, productANOVA_of_depends_not_subset μ T f hf S hS,
      zero_pow (by decide : 2 ≠ 0), FiniteProbabilityWeights.mean_const]

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

theorem productANOVAEnergy_smul (D : Finset (Finset I)) (c : ℝ) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D (fun y => c * f y) = c ^ 2 * productANOVAEnergy μ D f := by
  simp only [productANOVAEnergy, productANOVA_smul, mul_pow,
    FiniteProbabilityWeights.mean_const_mul, Finset.mul_sum]

theorem sqrt_productANOVAEnergy_smul (D : Finset (Finset I)) (c : ℝ) (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVAEnergy μ D (fun y => c * f y)) =
      |c| * Real.sqrt (productANOVAEnergy μ D f) := by
  rw [productANOVAEnergy_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProductEmbeddingConditional
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X : I → Type*} [∀ i, Fintype (X i)]

omit [Fintype I] [Fintype J] [∀ i, Fintype (X i)] in
theorem productCoordinateMix_embedding (e : J ↪ I) (S : Finset J) (x y : ∀ i, X i) :
    (fun j => productCoordinateMix (S.map e) x y (e j)) =
      productCoordinateMix S (fun j => x (e j)) (fun j => y (e j)) := by
  funext j
  by_cases hj : j ∈ S <;> simp [productCoordinateMix, hj]

theorem productConditionalMean_embedding (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ↪ I) (base : ∀ i, X i) (S : Finset J)
    (f : (∀ j, X (e j)) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ (S.map e) (fun y => f (fun j => y (e j))) x =
      productConditionalMean (fun j => μ (e j)) S f (fun j => x (e j)) := by
  simp only [productConditionalMean, productCoordinateMix_embedding]
  exact productMean_pullback μ e e.injective base
    (fun y => f (productCoordinateMix S (fun j => x (e j)) y))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductEmbeddingANOVA
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (e : J ↪ I) (base : ∀ i, X i)

include base

theorem productANOVA_embedding (S : Finset J) (f : (∀ j, X (e j)) → ℝ) (x : ∀ i, X i) :
    productANOVA μ (S.map e) (fun y => f (fun j => y (e j))) x =
      productANOVA (fun j => μ (e j)) S f (fun j => x (e j)) := by
  have happ (U : Finset J) : (Finset.mapEmbedding e).toEmbedding U = U.map e := rfl
  have hp : (S.map e).powerset = S.powerset.map (Finset.mapEmbedding e).toEmbedding := by
    simp only [Finset.map_eq_image, Finset.powerset_image]
    congr 1
    funext U
    exact (Finset.map_eq_image e U).symm
  unfold productANOVA
  rw [hp, Finset.sum_map]
  simp only [happ, Finset.card_map,
    ← Finset.map_sdiff, productConditionalMean_embedding μ e base]

theorem productANOVAEnergy_embedding (D : Finset (Finset J)) (f : (∀ j, X (e j)) → ℝ) :
    productANOVAEnergy μ (D.map (Finset.mapEmbedding e).toEmbedding) (fun y => f (fun j => y (e j))) =
      productANOVAEnergy (fun j => μ (e j)) D f := by
  have happ (U : Finset J) : (Finset.mapEmbedding e).toEmbedding U = U.map e := rfl
  unfold productANOVAEnergy
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro S _
  simp only [happ, productANOVA_embedding μ e base]
  exact productMean_pullback μ e e.injective base (fun y => productANOVA (fun j => μ (e j)) S f y ^ 2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OutsideProductTransport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem conditioningCoreSupports_map_outside {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι) (B : ℕ) :
    conditioningCoreSupports K B =
      (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card)).map
        (Finset.mapEmbedding (Function.Embedding.subtype (fun i => i ∉ K))).toEmbedding := by
  classical
  ext S
  constructor
  · intro hS
    have hs : S ⊆ Kᶜ ∧ S.card ≤ B - K.card := by
      simpa only [conditioningCoreSupports, Finset.mem_filter, Finset.mem_powerset] using hS
    let U := S.subtype (fun i => i ∉ K)
    have hu : U.map (Function.Embedding.subtype (fun i => i ∉ K)) = S :=
      Finset.subtype_map_of_mem (fun i hi => Finset.mem_compl.mp (hs.1 hi))
    have hc : U.card = S.card := by rw [← hu, Finset.card_map]
    apply Finset.mem_map.mpr
    refine ⟨U, (mem_lowDegreeCoordinateSets _ _ U).mpr (by rw [hc]; exact hs.2), ?_⟩
    exact hu
  · intro hS
    obtain ⟨U, hU, rfl⟩ := Finset.mem_map.mp hS
    change U.map (Function.Embedding.subtype (fun i => i ∉ K)) ∈ conditioningCoreSupports K B
    simp only [conditioningCoreSupports, Finset.mem_filter, Finset.mem_powerset, Finset.card_map]
    refine ⟨?_, (mem_lowDegreeCoordinateSets _ _ U).mp hU⟩
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_compl.mpr j.property

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem lowDegreeCoordinateSets_filter_outside {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι) (b : ℕ) :
    (lowDegreeCoordinateSets ι b).filter (fun S => S ⊆ Kᶜ) = conditioningCoreSupports K (b + K.card) := by
  ext S
  have hb : b + K.card - K.card = b := by omega
  simp only [Finset.mem_filter, mem_lowDegreeCoordinateSets, conditioningCoreSupports,
    Finset.mem_powerset, hb]
  exact and_comm

theorem productANOVAEnergy_outside {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (K : Finset ι) (base : ∀ i, X i) (b : ℕ) (f : (∀ i : {i // i ∉ K}, X i.val) → ℝ) :
    productANOVAEnergy μ (lowDegreeCoordinateSets ι b) (fun x => f (fun i => x i.val)) =
      productANOVAEnergy (fun i : {i // i ∉ K} => μ i.val)
        (lowDegreeCoordinateSets {i // i ∉ K} b) f := by
  have hd : ProductDependsOn Kᶜ (fun x => f (fun i : {i // i ∉ K} => x i.val)) := by
    intro x y hxy
    exact congrArg f (funext (fun i => hxy i.val (Finset.mem_compl.mpr i.property)))
  rw [productANOVAEnergy_of_depends_filter μ Kᶜ _ hd, lowDegreeCoordinateSets_filter_outside,
    conditioningCoreSupports_map_outside]
  have hb : b + K.card - K.card = b := by omega
  rw [hb]
  exact productANOVAEnergy_embedding μ (Function.Embedding.subtype (fun i => i ∉ K)) base _ f

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

theorem primeCoordinateReference_fiber {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x =
      (((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ)⁻¹ := by
  change productFiberMass (FiniteProbabilityWeights.pi
    (fun i => FiniteProbabilityWeights.uniform (σ → ZMod (q i)))).weight I x = _
  rw [productFiberMass_uniform]
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, Nat.cast_prod,
    Finset.prod_inv_distrib, Finset.prod_pow]

end Erdos3

end

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

theorem residuePrimeCoordinateMassRatio_eq_count {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMassRatio lo N M a q I x =
      ((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ *
        Fintype.card (ResiduePrimeCoordinateCell lo N M a q I x) /
        Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) := by
  rw [residuePrimeCoordinateMassRatio, primeCoordinateReference_fiber, div_inv_eq_mul]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCellNormLengths
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMassRatio_outside {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (S : Finset {i // i ∉ K}) (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    residuePrimeCoordinateMassRatio lo N M a q (K ∪ S.image Subtype.val) x =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        residuePrimeCoordinateMassRatio lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
          (fun i : {i // i ∉ K} => q i.val) S (fun i => x i.val) := by
  classical
  have hdis : Disjoint K (S.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hj
    exact j.property (heq ▸ hi)
  have hprod : (∏ i ∈ K ∪ S.image Subtype.val, q i) =
      (∏ i ∈ K, q i) * (∏ i ∈ S, q i.val) := by
    rw [Finset.prod_union hdis, Finset.prod_image]
    intro i _ j _ hij
    exact Subtype.ext hij
  have hc := Fintype.card_congr (residuePrimeCoordinateOutsideEquiv lo N M a q hpair K base u S x hx)
  have hb := Fintype.card_congr (residuePrimeCoordinateCell_lcmEquiv lo N M a q hpair K base u)
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base) := ⟨u⟩
  let : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) := ⟨u.val⟩
  have hK : (Fintype.card (ResiduePrimeCoordinateCell lo N M a q K base) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := ResiduePrimeCoordinateCell lo N M a q K base)
  have hB : (Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a)
  rw [residuePrimeCoordinateMassRatio_eq_count, residuePrimeCoordinateMassRatio_eq_count,
    residuePrimeCoordinateMassRatio_eq_count, hprod, Nat.cast_mul, mul_pow, hc, ← hb]
  field_simp

theorem residuePrimeCoordinateDensity_conditional_outside {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (f : (σ → ℤ) → ℝ) (S : Finset {i // i ∉ K})
    (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) (K ∪ S.image Subtype.val)
      (residuePrimeCoordinateDensity lo N M a hne q f) x =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        productConditionalMean (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)) S
          (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
            (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
            (fun i : {i // i ∉ K} => q i.val) f) (fun i => x i.val) := by
  have hm := Fintype.expect_equiv (residuePrimeCoordinateOutsideEquiv lo N M a q hpair K base u S x hx)
    (fun z => f (fun j => (z.val j).val)) (fun z => f (fun j => (z.val j).val)) (fun _ => rfl)
  rw [residuePrimeCoordinateDensity_conditional, residuePrimeCoordinateDensity_conditional,
    residuePrimeCoordinateMassRatio_outside lo N M a q hpair K base u S x hx, hm, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueCellOutsideDensity_lcm {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ) :
    residueCellOutsideDensity lo N M a q K base u f =
      residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) f := by
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base) := ⟨u⟩
  let := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  exact uniform_observedProductDensity_source_equiv
    (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
    (residuePrimeCoordinateCell_lcmEquiv lo N M a q hpair K base u)
    (fun z => primeCoordinateObservation (fun i : {i // i ∉ K} => q i.val) (fun k => (z k).val))
    (fun z => f (fun k => (z k).val))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMaskedInitialShell
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)

include hpair u

theorem residuePrimeCoordinateDensity_fixed (f : (σ → ℤ) → ℝ)
    (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    residuePrimeCoordinateDensity lo N M a hne q f x =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        residueCellOutsideDensity lo N M a q K base u f (fun i => x i.val) := by
  have hcover : K ∪ (Finset.univ : Finset {i // i ∉ K}).image Subtype.val = Finset.univ := by
    ext i
    by_cases hi : i ∈ K
    · simp [hi]
    · simp only [Finset.mem_union, hi, false_or, Finset.mem_image, Finset.mem_univ, iff_true]
      exact ⟨⟨i, hi⟩, trivial, rfl⟩
  have h := residuePrimeCoordinateDensity_conditional_outside lo N M a hne q hpair K base u f
    (Finset.univ : Finset {i // i ∉ K}) x hx
  rw [hcover, productConditionalMean_univ, productConditionalMean_univ] at h
  rw [residueCellOutsideDensity_lcm lo N M a q hpair K base u f]
  exact h

theorem residuePrimeCoordinateDensity_section (f : (σ → ℤ) → ℝ) (x : ∀ i, σ → ZMod (q i)) :
    productSectionAverage (primeCoordinateReference (σ := σ) q) K K base
      (residuePrimeCoordinateDensity lo N M a hne q f) x =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        residueCellOutsideDensity lo N M a q K base u f (fun i => x i.val) := by
  have hx : ∀ i ∈ K, productCoordinateMix K base x i = base i := by
    intro i hi
    simp only [productCoordinateMix, hi, ite_true]
  have hout : (fun i : {i // i ∉ K} => productCoordinateMix K base x i.val) = (fun i : {i // i ∉ K} => x i.val) := by
    funext i
    simp only [productCoordinateMix, i.property, ite_false]
  rw [productSectionAverage_eq_conditionalMean _ K K (Finset.Subset.refl K)]
  simp only [Finset.union_compl, productConditionalMean_univ]
  rw [residuePrimeCoordinateDensity_fixed lo N M a hne q hpair K base u f _ hx, hout]

omit hne hpair in
theorem residuePrimeCoordinateMassRatio_pos : 0 < residuePrimeCoordinateMassRatio lo N M a q K base := by
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base) := ⟨u⟩
  let : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) := ⟨u.val⟩
  have hp : 0 < ∏ i ∈ K, q i := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))
  rw [residuePrimeCoordinateMassRatio_eq_count]
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residuePrimeCoordinateDensity_section_norm_s2_oai {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ) (B : ℕ) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) q) (lowDegreeCoordinateSets ι B)
      (productSectionAverage (primeCoordinateReference (σ := σ) q) K K base
        (residuePrimeCoordinateDensity lo N M a hne q f))) =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
          (lowDegreeCoordinateSets {i // i ∉ K} B) (residueCellOutsideDensity lo N M a q K base u f)) := by
  have hs := funext (residuePrimeCoordinateDensity_section lo N M a hne q hpair K base u f)
  rw [hs, sqrt_productANOVAEnergy_smul,
    productANOVAEnergy_outside (primeCoordinateReference (σ := σ) q) K base B,
    abs_of_nonneg (residuePrimeCoordinateMassRatio_pos lo N M a q K base u).le]
  rfl

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.residuePrimeCoordinateDensity_section_norm_s2_oai.{u_1, u_2} := @OAI.Erdos3.residuePrimeCoordinateDensity_section_norm_s2_oai.{u_1, u_2}
