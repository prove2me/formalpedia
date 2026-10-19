-- Prove2me | solution 1 for OAI.Erdos3.stable_residue_kernel_total_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:17:04.241835+00:00
-- url     : https://prove2.me/submissions/85a13d8f-8010-40ae-80d0-763aa6e803d7

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_CylinderRemovalChain_kernel_total_pairing_le_s2
import Theorems.Thm_OAI_Erdos3_CylinderRemovalChain_uniform_section_bounds_s2
import Theorems.Thm_OAI_Erdos3_residuePrimeDensity_scaled_section_low_degree_s2
import Theorems.Thm_OAI_Erdos3_stable_site_normalized_marginals_s2
import Theorems.Thm_OAI_Erdos3_stable_site_reference_mean_bounds_s2

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

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem productCoordinateMix_weight_ne_zero (μ : ∀ i, FiniteProbabilityWeights (X i))
    (T : Finset I) (z x : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix T z x) ≠ 0 := by
  have h := mul_ne_zero hz hx
  rw [← productCoordinateMix_weight μ T z x] at h
  exact (mul_ne_zero_iff.mp h).1

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

theorem productSectionAverage_nonneg (T A : Finset I) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (hf : ∀ x, 0 ≤ f x) (x : ∀ i, X i) :
    0 ≤ productSectionAverage μ T A z f x :=
  (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => hf _)

theorem productConditionalMean_sectionAverage (T A B : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ B (productSectionAverage μ T A z f) x =
      productConditionalMean μ (A ∪ (B \ T)) f (productCoordinateMix T z x) := by
  change (FiniteProbabilityWeights.pi μ).mean (fun y => (FiniteProbabilityWeights.pi μ).mean
    (fun v => f (productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y)))) = _
  simp_rw [productCoordinateMix_section T A B hAT]
  exact productMean_coordinateMix μ Tᶜ
    (fun v => f (productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x) v))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_mono (T A : Finset I) (z : ∀ i, X i)
    (f g : (∀ i, X i) → ℝ) (h : ∀ x, f x ≤ g x) (x : ∀ i, X i) :
    productSectionAverage μ T A z f x ≤ productSectionAverage μ T A z g x :=
  (FiniteProbabilityWeights.pi μ).mean_mono (fun _ => h _)

theorem productSectionAverage_smul (T A : Finset I) (z : ∀ i, X i) (c : ℝ)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z (fun y => c * f y) x = c * productSectionAverage μ T A z f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul c _

theorem productSectionAverage_weighted_cap (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    0 ≤ productSectionAverage μ T A z (fun y => rho y * F y) x ∧
      productSectionAverage μ T A z (fun y => rho y * F y) x ≤
        M * productSectionAverage μ T A z rho x := by
  constructor
  · exact productSectionAverage_nonneg μ T A z _ (fun y => mul_nonneg (hrho y) (hF y).1) x
  · calc
      _ ≤ productSectionAverage μ T A z (fun y => M * rho y) x :=
        productSectionAverage_mono μ T A z _ _ (fun y => by
          simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hF y).2 (hrho y)) x
      _ = _ := productSectionAverage_smul μ T A z M rho x

theorem productSectionAverage_weighted_zero (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i)
    (hz : productSectionAverage μ T A z rho x = 0) :
    productSectionAverage μ T A z (fun y => rho y * F y) x = 0 := by
  have h := productSectionAverage_weighted_cap μ T A z rho F hrho hF x
  rw [hz, mul_zero] at h
  exact le_antisymm h.2 h.1

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem ProductMarginalsClose.mono {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s t : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (ht : t ≤ s) : ProductMarginalsClose μ rho eta t :=
  fun B hB x hx => h B (hB.trans ht) x hx

theorem ProductMarginalsClose.section {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (T A : Finset I) (hAT : A ⊆ T)
    (hAs : A.card ≤ s) (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) :
    ProductMarginalsClose μ (productSectionAverage μ T A z rho) eta (s - A.card) := by
  intro B hB x hx
  rw [productConditionalMean_sectionAverage μ T A B hAT]
  apply h
  · have hcard := Finset.card_union_le A (B \ T)
    have hdiff := Finset.card_le_card (Finset.sdiff_subset : B \ T ⊆ B)
    omega
  · exact productCoordinateMix_weight_ne_zero μ T z x hz hx

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionDensityWeight_nonneg (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x)
    (x : ∀ i, X i) : 0 ≤ productSectionDensityWeight μ T A z rho F x := by
  apply div_nonneg
  · exact productSectionAverage_nonneg μ T A z _ (fun y => mul_nonneg (hrho y) (hF y)) x
  · exact productSectionAverage_nonneg μ T A z rho hrho x

theorem productSectionDensityWeight_le (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productSectionDensityWeight μ T A z rho F x ≤ M := by
  unfold productSectionDensityWeight
  by_cases hz : productSectionAverage μ T A z rho x = 0
  · rw [hz, div_zero]
    exact hM
  · have hp : 0 < productSectionAverage μ T A z rho x :=
      lt_of_le_of_ne (productSectionAverage_nonneg μ T A z rho hrho x) (Ne.symm hz)
    exact (div_le_iff₀ hp).mpr (productSectionAverage_weighted_cap μ T A z rho F hrho hF x).2

theorem productSectionDensityWeight_mul (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productSectionAverage μ T A z rho x * productSectionDensityWeight μ T A z rho F x =
      productSectionAverage μ T A z (fun y => rho y * F y) x := by
  by_cases hz : productSectionAverage μ T A z rho x = 0
  · rw [hz, zero_mul, productSectionAverage_weighted_zero μ T A z rho F hrho hF x hz]
  · unfold productSectionDensityWeight
    field_simp

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

variable [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

theorem density_cut (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.cut F w) x =
      if c.Contains x then observedProductDensity μ p F w x else 0 := by
  classical
  by_cases hx : c.Contains x
  · rw [if_pos hx]
    change p.fiberMean F x (c.cut F w) / _ = p.fiberMean F x w / _
    congr 1
    unfold FiniteProbabilityWeights.fiberMean
    congr 1
    funext z
    by_cases hz : F z = x
    · simp [cut, hz, hx]
    · simp [hz]
  · rw [if_neg hx]
    have he : p.fiberMean F x (c.cut F w) = 0 := by
      calc
        _ = p.mean (fun _ => 0) := by
          unfold FiniteProbabilityWeights.fiberMean
          congr 1
          funext z
          by_cases hz : F z = x
          · simp [cut, hz, hx]
          · simp [hz]
        _ = 0 := p.mean_const 0
    change p.fiberMean F x (c.cut F w) / _ = 0
    rw [he, zero_div]

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)

theorem mass_cut_self : c.mass μ base (observedProductDensity μ p F (c.cut F w)) =
    c.mass μ base (observedProductDensity μ p F w) := by
  unfold mass productConditionalMean
  congr 1
  funext y
  rw [c.density_cut]
  apply if_pos
  intro i
  simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property

end Erdos3.ProductCylinder

end

section

namespace Erdos3

theorem CylinderRemovalChain.removed_size_mass {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), cf.1.1.card ≤ j ∧
      τ < cf.1.mass μ base (observedProductDensity μ p F cf.2) := by
  induction hchain with
  | nil =>
    intro cf hcf
    simp only [removedCylinderWeights, List.zip_nil_left, List.not_mem_nil] at hcf
  | @cons w v cs d hsize hmass hbounded rest ih =>
    intro cf hcf
    change cf ∈ (d, d.cut F w) :: cs.zip (removedCylinderWeights F (d.erase F w) cs) at hcf
    rcases List.mem_cons.mp hcf with hcf | hcf
    · subst cf
      exact ⟨hsize, by rwa [d.mass_cut_self μ base p F w]⟩
    · exact ih cf hcf

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ApproxMomentEnvelope
namespace OAI

section

namespace Erdos3

theorem approxMomentEnvelope_one_le (N r : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    1 ≤ approxMomentEnvelope N r M := by
  unfold approxMomentEnvelope
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (by have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith))
  · linarith

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

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSection_truncatedGram_bound (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (rho f : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    {M η : ℝ} (hM : 0 ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ rho η (2 * b + A.card)) :
    productANOVAEnergy μ D (productSectionAverage μ T A z (fun x => rho x * f x)) ≤
      2 * M * (FiniteProbabilityWeights.pi μ).mean
        (productSectionAverage μ T A z (fun x => rho x * f x)) +
      2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  have hc : ProductMarginalsClose μ (productSectionAverage μ T A z rho) η (2 * b) := by
    simpa only [Nat.add_sub_cancel] using
      ProductMarginalsClose.section μ hclose T A hAT (by omega) z hz
  have h := productTruncatedGram_bound μ (productSectionAverage μ T A z rho)
    (productSectionDensityWeight μ T A z rho f)
    (productSectionAverage_nonneg μ T A z rho hrho)
    (fun x => ⟨productSectionDensityWeight_nonneg μ T A z rho f hrho (fun y => (hf y).1) x,
      productSectionDensityWeight_le μ T A z rho f hrho hM hf x⟩) hη D hcard hc
  simpa only [productSectionDensityWeight_mul μ T A z rho f hrho hf] using h

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSection_truncatedGram_uniform (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (rho f : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    {M η : ℝ} (hM : 0 ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ rho η (2 * b + A.card)) :
    productANOVAEnergy μ D (productSectionAverage μ T A z (fun x => rho x * f x)) ≤
      2 * M ^ 2 * (1 + η) +
        2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  have hc := ProductMarginalsClose.section μ hclose T A hAT (by omega) z hz
  have hmean := hc ∅ (by simp) z hz
  rw [productConditionalMean_empty] at hmean
  have hmass : (FiniteProbabilityWeights.pi μ).mean
      (productSectionAverage μ T A z (fun x => rho x * f x)) ≤ M * (1 + η) := by
    calc
      _ ≤ (FiniteProbabilityWeights.pi μ).mean (fun x => M * productSectionAverage μ T A z rho x) :=
        (FiniteProbabilityWeights.pi μ).mean_mono
          (fun x => (productSectionAverage_weighted_cap μ T A z rho f hrho hf x).2)
      _ = M * (FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ T A z rho) :=
        (FiniteProbabilityWeights.pi μ).mean_const_mul M _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hmean).2]) hM
  have h := productSection_truncatedGram_bound μ T A hAT z hz rho f hrho hM hf hη D hcard hclose
  nlinarith [mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)]

theorem observedProductDensity_section_norm_uniform {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (w : Ω → ℝ) {M η : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card)) :
    Real.sqrt (productANOVAEnergy μ D (productSectionAverage μ T A z (observedProductDensity μ p F w))) ≤
      Real.sqrt (2 * M ^ 2 * (1 + η) +
        2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2) := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w M hM hw
  rw [he]
  apply Real.sqrt_le_sqrt
  exact productSection_truncatedGram_uniform μ T A hAT z hz
    (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (by intro x; norm_num)) hM hf hη D hcard hclose

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_section_norm_le_three (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (T A : Finset ι) (hAT : A ⊆ T) (z : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy μ D
      (productSectionAverage μ T A z (observedProductDensity μ p F w))) ≤ 3 := by
  have h := observedProductDensity_section_norm_uniform μ p F T A hAT z hz w
    zero_le_one hw hη0 D hcard hclose
  simp only [one_pow, mul_one] at h
  apply h.trans
  calc
    _ ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by linarith)
    _ = 3 := by norm_num

theorem observedProductDensity_scaled_section_norm (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) {scale cap : ℝ}
    (hscale : 0 < scale) (hcap : scale⁻¹ ≤ cap)
    (T A : Finset ι) (hAT : A ⊆ T) (z : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy μ D
      (fun y => scale⁻¹ * productSectionAverage μ T A z (observedProductDensity μ p F w) y)) ≤ 3 * cap := by
  rw [sqrt_productANOVAEnergy_smul, abs_of_nonneg (inv_nonneg.mpr hscale.le)]
  have h := observedProductDensity_section_norm_le_three μ p F w hw T A hAT z hz
    hη0 hη1 D hcard hclose herr
  calc
    _ ≤ scale⁻¹ * 3 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hscale.le)
    _ ≤ 3 * cap := by nlinarith

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

theorem residuePrimeCoordinateMean_re {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    (residuePrimeCoordinateMean f lo N M a q I x).re =
      𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, (f (fun j => (z.val j).val)).re := by
  simp only [residuePrimeCoordinateMean, Fintype.expect_eq_sum_div_card,
    Complex.div_natCast_re, Complex.re_sum]
  congr 3 <;> exact Subsingleton.elim _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityNormalizationScales
namespace OAI

section

namespace Erdos3

theorem log_two_add_le_of_le_exp {x P : ℝ} (hx : 0 ≤ x) (hP : 0 ≤ P)
    (hbound : x ≤ Real.exp P) : Real.log (2 + x) ≤ P + 2 := by
  have he : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hh : 2 + x ≤ Real.exp (P + 2) := by
    rw [Real.exp_add]
    calc
      2 + x ≤ 3 * Real.exp P := by linarith
      _ ≤ Real.exp P * Real.exp 2 := by nlinarith [Real.exp_pos P]
  exact (Real.log_le_log (by positivity) hh).trans_eq (Real.log_exp _)

theorem baseline_scale_inv_le {v τ : ℝ} (hv : 0 ≤ v) (hτ : 0 < τ) :
    (2 * (v + τ))⁻¹ ≤ τ⁻¹ := by
  simpa only [one_div] using one_div_le_one_div_of_le hτ (by linarith : τ ≤ 2 * (v + τ))

theorem weighted_scale_inv_le {v τ level : ℝ} (hv : 0 ≤ v) (hτ : 0 < τ) (hl : 0 < level) :
    (4 * level * (v + τ))⁻¹ ≤ level⁻¹ * τ⁻¹ := by
  have h := one_div_le_one_div_of_le (mul_pos hl hτ)
    (show level * τ ≤ 4 * level * (v + τ) by nlinarith)
  simpa only [one_div, mul_inv_rev, mul_comm] using h

theorem site_normalization_caps {v τ level L T : ℝ}
    (hv : 0 ≤ v) (hτ : 0 < τ) (hl : 0 < level) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hlevel : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T) :
    0 < 2 * (v + τ) ∧ 0 < 4 * level * (v + τ) ∧
    (2 * (v + τ))⁻¹ ≤ Real.exp (L + T) ∧
    (4 * level * (v + τ))⁻¹ ≤ Real.exp (L + T) ∧
    Real.log (2 + Real.exp (L + T)) ≤ L + T + 2 := by
  have hlinv : level⁻¹ ≤ Real.exp L := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (-L)) hlevel
    simpa only [one_div, Real.exp_neg, inv_inv] using hh
  have hbase : (2 * (v + τ))⁻¹ ≤ Real.exp (L + T) :=
    (baseline_scale_inv_le hv hτ).trans (hτinv.trans (Real.exp_le_exp.mpr (by linarith)))
  have hweighted : (4 * level * (v + τ))⁻¹ ≤ Real.exp (L + T) := by
    rw [Real.exp_add]
    exact (weighted_scale_inv_le hv hτ hl).trans
      (mul_le_mul hlinv hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos L).le)
  exact ⟨by positivity, by positivity, hbase, hweighted,
    log_two_add_le_of_le_exp (Real.exp_pos _).le (add_nonneg hL hT) le_rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CylinderShellCountBudget
namespace OAI

section

namespace Erdos3

theorem uniform_section_norm_product_le_exp {τ L T : ℝ} (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp T) :
    (3 * τ⁻¹) * (3 * Real.exp (L + T)) ≤ Real.exp (L + 2 * T + 4) := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hM : 3 * τ⁻¹ ≤ Real.exp (T + 2) := by
    rw [Real.exp_add]
    exact (mul_le_mul h3 hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hN : 3 * Real.exp (L + T) ≤ Real.exp (L + T + 2) := by
    rw [Real.exp_add (L + T) 2]
    exact (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  calc
    _ ≤ Real.exp (T + 2) * Real.exp (L + T + 2) := mul_le_mul hM hN (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

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

variable {ι σ : Type*} [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
  (moduli : ι → ℕ) [∀ i, NeZero (moduli i)]
  (f : (σ → ℤ) → ℝ) (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)

include hf

theorem residuePrimeDensity_scaled_section_norm {scale cap η : ℝ}
    (hscale : 0 < scale) (hinv : scale⁻¹ ≤ cap) (A : Finset ι) (z : ∀ i, σ → ZMod (moduli i))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) moduli) D
      (fun y => scale⁻¹ * productSectionAverage (primeCoordinateReference (σ := σ) moduli) A A z
        (residuePrimeCoordinateDensity lo N M a hne moduli f) y)) ≤ 3 * cap := by
  let := hne
  have hphys : ∀ z : IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a,
      0 ≤ f (fun j => (z j).val) ∧ f (fun j => (z j).val) ≤ 1 := by
    intro z
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro j
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z j).property).1)
  exact observedProductDensity_scaled_section_norm (primeCoordinateReference (σ := σ) moduli)
    (FiniteProbabilityWeights.uniform (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation moduli (fun j => (z j).val)) (fun z => f (fun j => (z j).val))
    hphys hscale hinv A A le_rfl z
    (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos moduli i (z i))).ne'
    hη0 hη1 D hcard hclose herr

theorem residuePrimeDensity_section_norm_le_three (A : Finset ι) (z : ∀ i, σ → ZMod (moduli i))
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) moduli) D
      (productSectionAverage (primeCoordinateReference (σ := σ) moduli) A A z
        (residuePrimeCoordinateDensity lo N M a hne moduli f))) ≤ 3 := by
  let := hne
  have hphys : ∀ z : IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a,
      0 ≤ f (fun j => (z j).val) ∧ f (fun j => (z j).val) ≤ 1 := by
    intro z
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro j
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z j).property).1)
  exact observedProductDensity_section_norm_le_three (primeCoordinateReference (σ := σ) moduli)
    (FiniteProbabilityWeights.uniform (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation moduli (fun j => (z j).val)) (fun z => f (fun j => (z j).val))
    hphys A A le_rfl z
    (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos moduli i (z i))).ne'
    hη0 hη1 D hcard hclose herr

end Erdos3

end

section

namespace Erdos3

theorem productSectionAverage_empty_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) : productSectionAverage μ ∅ ∅ z f = f := by
  funext x
  have hm (u v : ∀ i, X i) : productCoordinateMix (∅ : Finset ι) u v = v := by
    funext i
    simp [productCoordinateMix]
  simp only [productSectionAverage, hm]
  exact (FiniteProbabilityWeights.pi μ).mean_const _

theorem residuePrimeDensity_norm_le_three {ι σ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) q) D
      (residuePrimeCoordinateDensity lo N M a hne q f)) ≤ 3 := by
  have h := residuePrimeDensity_section_norm_le_three lo N M a hne q f hf ∅ (fun _ _ => 0)
    hη0 hη1 D hcard (by simpa only [Finset.card_empty, add_zero] using hclose) herr
  rw [productSectionAverage_empty_fixed] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StableRetainedAtom
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_re_nonneg {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re) :
    0 ≤ (residuePrimeCoordinateMean g lo N M a q K base).re := by
  rw [residuePrimeCoordinateMean_re, Fintype.expect_eq_sum_div_card]
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro z _
  apply hg
  apply (mem_translatedIntegerBox lo N _).mpr
  intro j
  exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z.val j).property).1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.StableSiteLowDegree
namespace OAI

section

namespace Erdos3

theorem approxMomentEnvelope_pow_le_exp (N r q : ℕ) (M P : ℝ)
    (hP : 0 ≤ P) (hM0 : 0 ≤ M) (hN : (N : ℝ) ≤ Real.exp P) (hM : M ≤ Real.exp P)
    (hr : (r : ℝ) ≤ P) (hq : (q : ℝ) ≤ P + 2) :
    approxMomentEnvelope N r M ^ q ≤ Real.exp ((P + 3) ^ 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hone : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hadd (x : ℝ) (hx : x ≤ Real.exp P) : 2 + x ≤ Real.exp (P + 2) := by
    calc
      _ ≤ 3 * Real.exp P := by linarith
      _ ≤ Real.exp 2 * Real.exp P := mul_le_mul_of_nonneg_right hthree (Real.exp_pos P).le
      _ = _ := by rw [mul_comm, ← Real.exp_add]
  have henv : approxMomentEnvelope N r M ≤ Real.exp ((P + 3) ^ 2) := by
    calc
      _ ≤ Real.exp 1 ^ (r + 1) * Real.exp (P + 2) ^ r * Real.exp (P + 2) := by
        unfold approxMomentEnvelope
        gcongr
        · exact hadd N hN
        · exact hadd M hM
      _ = Real.exp (((r : ℝ) + 1) * (P + 3)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp ((P + 3) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right (show (r : ℝ) + 1 ≤ P + 3 by linarith)
          (show 0 ≤ P + 3 by linarith)]
  calc
    _ ≤ Real.exp ((P + 3) ^ 2) ^ q :=
      pow_le_pow_left₀ ((zero_le_one.trans (approxMomentEnvelope_one_le N r hM0))) henv q
    _ = Real.exp ((q : ℝ) * (P + 3) ^ 2) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((P + 3) ^ 3) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (show (q : ℝ) ≤ P + 3 by linarith) (sq_nonneg (P + 3))]

theorem approxMoment_small_of_exponential (N r q : ℕ) (M P : ℝ)
    (hP : 0 ≤ P) (hM0 : 0 ≤ M) (hN : (N : ℝ) ≤ Real.exp P) (hM : M ≤ Real.exp P)
    (hr : (r : ℝ) ≤ P) (hq : (q : ℝ) ≤ P + 2) {η : ℝ}
    (hη : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3))) :
    η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (N : ℝ)) ^ r * (2 + M)) ^ q)⁻¹ := by
  have hpos : 0 < approxMomentEnvelope N r M ^ q :=
    pow_pos (zero_lt_one.trans_le (approxMomentEnvelope_one_le N r hM0)) q
  have hbound := approxMomentEnvelope_pow_le_exp N r q M P hP hM0 hN hM hr hq
  have hinv : Real.exp (-((P + 3) ^ 3)) ≤ (approxMomentEnvelope N r M ^ q)⁻¹ := by
    simpa only [one_div, Real.exp_neg] using one_div_le_one_div_of_le hpos hbound
  exact hη.trans (mul_le_mul_of_nonneg_left hinv (by norm_num))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StableSiteSectionLengths
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem stable_site_uniform_sections {ι σ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {j r b moment : ℕ} {level inc δ η τ L T P : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ / 8) (hinc : inc ≤ level * τ / 8)
    (hη0 : 0 ≤ η) (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T)
    (hlog : L + T + 2 ≤ P) (hrP : ((j + r : ℕ) : ℝ) ≤ P)
    (hmoment : 2 ≤ moment) (heven : Even moment) (hPq : P ≤ (moment : ℝ)) (hqP : (moment : ℝ) ≤ P + 2)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ j + r →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    let v := (residuePrimeCoordinateMean g lo N M a q K base).re
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    ∀ S : Finset {i // i ∉ K}, S.card ≤ j → ∀ x,
      productConditionalMean ν S (density (fun z => (h z).re)) x ≤
        level * productConditionalMean ν S (density (fun z => (g z).re)) x + level * τ ∧
      v - τ ≤ productConditionalMean ν S (density (fun z => (g z).re)) x ∧
      (∀ k, k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
        (fun y => (4 * level * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (h z).re)) y)) ≤
          (16 * (P + 2)) ^ (2 * k)) ∧
      (∀ k, k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
        (fun y => (2 * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (g z).re)) y)) ≤
          (16 * (P + 2)) ^ (2 * k)) ∧
      Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets {i // i ∉ K} b)
        (fun y => (4 * level * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (h z).re)) y)) ≤
          3 * Real.exp (L + T) ∧
      Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets {i // i ∉ K} b)
        (fun y => (2 * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (g z).re)) y)) ≤
          3 * Real.exp (L + T) := by
  dsimp only
  have hga : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hg z hz).1]
    exact (hg z hz).2
  have hha : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hh z hz).1]
    exact (hh z hz).2
  have hmeans := stable_site_reference_mean_bounds_s2 hstable hupper hM hpair hcop u hga hha
    hlevel.le hτ.le hδ hinc hη hητ hηlevel herror
  obtain ⟨hgb, hhb⟩ := stable_site_normalized_marginals_s2 hstable hupper hM hpair hcop u hg hha
    hlevel hτ (by linarith) (by nlinarith) hη (by linarith) (by nlinarith) herror
  have hv := residuePrimeCoordinateMean_re_nonneg g lo N M a q K base (fun z hz => (hg z hz).1)
  obtain ⟨hgs, hhs, hgcap, hhcap, hlogcap⟩ := site_normalization_caps hv hτ hlevel hL hT hlower hτinv
  have hP : 0 ≤ P := (Nat.cast_nonneg (j + r)).trans hrP
  have hcapP : Real.exp (L + T) ≤ Real.exp P := Real.exp_le_exp.mpr (by linarith)
  have houtside : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcount
  have hbudget := approxMoment_small_of_exponential (Fintype.card {i // i ∉ K}) (j + r) moment
    (Real.exp (L + T)) P hP (Real.exp_pos _).le houtside hcapP hrP hqP hηsmall
  have hclow := ProductMarginalsClose.mono _ hclose (le_max_left _ _)
  have hne := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  intro S hS x
  have hSj : S.card ≤ j + r := by omega
  have hm := hmeans S hSj x
  refine ⟨hm.1, hm.2, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact residuePrimeDensity_scaled_section_low_degree_s2 lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (h z).re) hh
      hhs (Real.exp_pos _).le hhcap hmoment heven S hSj (by omega) x hη0 hrP (hlogcap.trans hlog)
      hPq hqP hbudget hclow hhb
  · intro k hk
    exact residuePrimeDensity_scaled_section_low_degree_s2 lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (g z).re) hg
      hgs (Real.exp_pos _).le hgcap hmoment heven S hSj (by omega) x hη0 hrP (hlogcap.trans hlog)
      hPq hqP hbudget hclow hgb
  · exact residuePrimeDensity_scaled_section_norm lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (h z).re) hh
      hhs hhcap S x hη0 hη.le _ (fun A hA => (mem_lowDegreeCoordinateSets _ b A).mp hA)
      (ProductMarginalsClose.mono _ hclose (by omega)) hgram
  · exact residuePrimeDensity_scaled_section_norm lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (g z).re) hg
      hgs hgcap S x hη0 hη.le _ (fun A hA => (mem_lowDegreeCoordinateSets _ b A).mp hA)
      (ProductMarginalsClose.mono _ hclose (by omega)) hgram

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StableResidueKernelTotal
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem stable_residue_kernel_total_s2_oai {Ω ι σ : Type*}
    [Fintype Ω]
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {j r b moment : ℕ} {level inc δ η τ L T P : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    {X : {i // i ∉ K} → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (sourceBase : ∀ i, X i)
    (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    {regK κ ε ξ shell Q : ℝ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ sourceBase p F regK τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hregK : 1 ≤ regK)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1) (hmass : p.mean rem ≤ τ)
    (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ / 8) (hinc : inc ≤ level * τ / 8)
    (hη0 : 0 ≤ η) (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T)
    (hlog : L + T + 2 ≤ P) (hrP : ((j + r : ℕ) : ℝ) ≤ P)
    (hmoment : 2 ≤ moment) (heven : Even moment) (hPq : P ≤ (moment : ℝ)) (hqP : (moment : ℝ) ≤ P + 2)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ j + r →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)
    (hsourceclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hresGram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (kernel : ∀ i : {i // i ∉ K}, X i → FiniteProbabilityWeights (σ → ZMod (q i.val)))
    (C : {i // i ∉ K} → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i : {i // i ∉ K}, ∀ f : (σ → ZMod (q i.val)) → ℝ,
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean f = 0 →
      (μ i).mean (fun x => (kernel i x).mean f ^ 2) ≤ C i *
        (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean (fun y => f y ^ 2))
    (hK : ∀ i : {i // i ∉ K}, ∀ f : (σ → ZMod (q i.val)) → ℝ, (μ i).mean (fun x => (kernel i x).mean f) =
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean f)
    (hε : 0 ≤ ε) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hslack : ξ * (2 + ε) ≤ ε)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i, C i ≤ κ ^ 2)
    (hlow : κ * (8 * (1 + regK) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16)
    (hrtail : CyclicCrootSisask.spectralIterations ξ (L + 2 * T + 4) ≤ r) (hrb : j + r ≤ b)
    (hshell : 0 < shell) (hb : j + CyclicCrootSisask.spectralIterations shell Q ≤ b)
    (hbudget : ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, σ → ZMod (q i.val.val)) : ℝ) *
        (cf.1.mass μ sourceBase (observedProductDensity μ p F cf.2) * level *
          ((residuePrimeCoordinateMean g lo N M a q K base).re + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))).sum ≤ Real.exp Q) :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (kernel i) (hK i)
    productTruncatedPairing c (lowDegreeCoordinateSets {i // i ∉ K} b) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (3 + (1 + ε) * level * 3) := by
  dsimp only
  let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
  have hsite := stable_site_uniform_sections hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc
    hη0 hη hητ hηlevel hL hT hlower hτinv hlog hrP hmoment heven hPq hqP hcount hηsmall herror hclose hgram
  have hv := residuePrimeCoordinateMean_re_nonneg g lo N M a q K base (fun z hz => (hg z hz).1)
  have hP : 0 ≤ P := (Nat.cast_nonneg (j + r)).trans hrP
  have hrP' : (r : ℝ) ≤ P := by
    have h : (r : ℝ) ≤ ((j + r : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left r j
    exact h.trans hrP
  have hlog' : Real.log (2 + τ⁻¹) ≤ P :=
    (log_two_add_le_of_le_exp (inv_nonneg.mpr hτ.le) hT hτinv).trans (by linarith)
  have houtside : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcount
  have hsampleSmall := approxMoment_small_of_exponential (Fintype.card {i // i ∉ K}) r moment τ⁻¹ P
    hP (inv_nonneg.mpr hτ.le) houtside (hτinv.trans (Real.exp_le_exp.mpr (by linarith))) hrP' hqP hηsmall
  have horder : j + r * (moment + 1) ≤ (j + r) * (moment + 1) := by nlinarith
  have hsample := hchain.uniform_section_bounds_s2 hμ hregK hτ hη0 hη.le hmoment heven hrP' hlog' hPq hqP
    hsampleSmall (ProductMarginalsClose.mono μ hsourceclose
      (max_le (horder.trans (le_max_left _ _)) (le_max_right _ _))) hgram hw
  have hne := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  have hHnorm := residuePrimeDensity_norm_le_three lo N (M.lcm (∏ i ∈ K, q i))
    (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (h z).re) hh
    hη0 hη.le (lowDegreeCoordinateSets {i // i ∉ K} b)
    (fun S hS => (mem_lowDegreeCoordinateSets _ b S).mp hS)
    (ProductMarginalsClose.mono ν hclose (by omega)) hgram
  have hGnorm := residuePrimeDensity_norm_le_three lo N (M.lcm (∏ i ∈ K, q i))
    (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (g z).re) hg
    hη0 hη.le (lowDegreeCoordinateSets {i // i ∉ K} b)
    (fun S hS => (mem_lowDegreeCoordinateSets _ b S).mp hS)
    (ProductMarginalsClose.mono ν hclose (by omega)) hgram
  apply CylinderRemovalChain.kernel_total_pairing_le_s2 μ ν kernel C hC hbound hK hchain hμ siteBase
    (fun z => (hw z).2) hrem hmass (by positivity) (by positivity) hv hτ hlevel hε hξ hξ1 hslack
    hκ0 hκhalf hcap hlow (uniform_section_norm_product_le_exp hτ hτinv) hrtail hrb hη0
    (ProductMarginalsClose.mono μ hsourceclose (by omega)) hresGram
    _ _ hHnorm hGnorm hshell hb hbudget
  intro cf hcf
  obtain ⟨hwl, hwn⟩ := hsample cf hcf
  refine ⟨fun k _ hk => hwl k hk, hwn, ?_⟩
  intro z
  obtain ⟨hHm, hGm, hhl, hgl, hhn, hgn⟩ := hsite cf.1.1 (hchain.removed_size_mass cf hcf).1
    (productSubtypePoint cf.1.1 z siteBase)
  exact ⟨hHm, hGm, fun k _ hk => hhl k hk, fun k _ hk => hgl k hk, hhn, hgn⟩

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.stable_residue_kernel_total_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.stable_residue_kernel_total_s2_oai.{u_1, u_2, u_3, u_4}
