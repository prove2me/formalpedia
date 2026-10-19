-- Prove2me | solution 1 for OAI.Erdos3.residue_initial_conditioning_shell_of_lengths_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:56:57.036898+00:00
-- url     : https://prove2.me/submissions/429a0806-0172-4794-a988-4de2b77b5f79

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B197
import Theorems.Thm_OAI_Erdos3_residue_initial_conditioning_shell_s2
import Theorems.Thm_OAI_Erdos3_retained_residue_marginals_of_lengths_s2

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

theorem affineComparisonAccuracy_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P L T : ℝ} (b : ℕ) (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) :
    2 * affineComparisonAccuracy b P L T * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + affineComparisonAccuracy b P L T) ^ 2 ≤ Real.exp (-T) := by
  let η := affineComparisonAccuracy b P L T
  have he := affineComparisonAccuracy_bounds (level := Real.exp (-L)) b hP hL hT le_rfl
  have hη0 : 0 < η := he.1
  have hη1 : η < 1 := he.2.1
  have hc := lowDegreeCoordinateSets_card_le_exp hP hcount b
  have hc2 : ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 ≤
      Real.exp (2 * (b : ℝ) * (P + 1)) := by
    calc
      _ ≤ (Real.exp ((b : ℝ) * (P + 1))) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) htwo 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hp4 : (4 : ℝ) ^ b ≤ Real.exp (2 * (b : ℝ)) := by
    exact (pow_le_pow_left₀ (by norm_num) hfour b).trans_eq (by rw [← Real.exp_nat_mul]; congr 1; ring)
  have hsq : (1 + η) ^ 2 ≤ 4 := by nlinarith
  have hsmall : η ≤ Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) / 8 := by
    apply exp_neg_le_exp_neg_div_eight
    unfold affineComparisonAccuracyLog
    have hp : 0 ≤ (P + 3) ^ 3 := by positivity
    linarith
  change 2 * η * _ ^ 2 * _ ^ b * (1 + η) ^ 2 ≤ _
  calc
    _ ≤ 2 * η * Real.exp (2 * (b : ℝ) * (P + 1)) * Real.exp (2 * (b : ℝ)) * 4 := by gcongr
    _ = 8 * η * (Real.exp (2 * (b : ℝ) * (P + 1)) * Real.exp (2 * (b : ℝ))) := by ring
    _ = 8 * η * Real.exp (2 * (b : ℝ) * (P + 2)) := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ 8 * (Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) / 8) * Real.exp (2 * (b : ℝ) * (P + 2)) := by gcongr
    _ = Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) * Real.exp (2 * (b : ℝ) * (P + 2)) := by ring
    _ = Real.exp (-T) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCellNormLengths
namespace OAI

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

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueCellOutsideDensity_norm_of_lengths {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i)) (hcop : ∀ i ∉ K, M.Coprime (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ)
    (hf : ∀ z : ResiduePrimeCoordinateCell lo N M a q K base,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (B : ℕ) (P modLog dimLog : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
    (hlength : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimLog + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ)) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (lowDegreeCoordinateSets {i // i ∉ K} B) (residueCellOutsideDensity lo N M a q K base u f)) ≤ 3 := by
  let η := affineComparisonAccuracy B P 0 0
  let μ := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
  let p := @FiniteProbabilityWeights.uniform (ResiduePrimeCoordinateCell lo N M a q K base) _ ⟨u⟩
  let F := fun z : ResiduePrimeCoordinateCell lo N M a q K base =>
    primeCoordinateObservation (fun i : {i // i ∉ K} => q i.val) (fun k => (z.val k).val)
  have he := affineComparisonAccuracy_bounds (level := 1) (L := 0) (T := 0) B hP (by norm_num) (by norm_num) (by norm_num)
  have hcount' : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcount
  have hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} B).card : ℝ) ^ 2 *
      (4 : ℝ) ^ B * (1 + η) ^ 2 ≤ 1 := by
    simpa only [neg_zero, Real.exp_zero] using
      affineComparisonAccuracy_gram (ι := {i // i ∉ K}) (L := 0) (T := 0) B hP (by norm_num) (by norm_num) hcount'
  have hbase0 := retained_residue_marginals_of_lengths_s2 (ι := ι) (σ := σ)
    lo N M a q hM hpair K base hcop u (2 * B) modLog dimLog (affineComparisonAccuracyLog B P 0 0) η
  have herror : Real.exp (-affineComparisonAccuracyLog B P 0 0) ≤ η := by
    unfold η affineComparisonAccuracy
    exact le_rfl
  have hbase := (hbase0 hmodLog he.2.1.le herror hmoduli hdim hlength).1
  have hclose : ProductMarginalsClose μ (residueCellOutsideDensity lo N M a q K base u (fun _ => 1)) η (2 * B) := by
    rw [residueCellOutsideDensity_lcm lo N M a q hpair K base u]
    exact hbase
  change ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * B) at hclose
  have hz : (FiniteProbabilityWeights.pi μ).weight (fun _ _ => 0) ≠ 0 :=
    (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos (fun i : {i // i ∉ K} => q i.val) i (fun _ => 0))).ne'
  have hn := observedProductDensity_section_norm_le_three μ p F (fun z => f (fun k => (z.val k).val)) hf
    ∅ ∅ (Finset.Subset.refl ∅) (fun _ _ => 0) hz he.1.le he.2.1.le
    (lowDegreeCoordinateSets {i // i ∉ K} B) (fun S hS => (mem_lowDegreeCoordinateSets _ _ S).mp hS)
    (by simpa only [Finset.card_empty, add_zero] using hclose) hgram
  rw [productSectionAverage_empty_fixed] at hn
  exact hn

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

theorem residue_initial_conditioning_shell_of_lengths_s2_oai {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (loX : σ → ℤ) (NX : σ → ℕ) (MX : ℕ) (aX : σ → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : τ → ℤ) (NY : τ → ℕ) (MY : ℕ) (aY : τ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, σ → ZMod (q i)) (baseY : ∀ i, τ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (kernel : ∀ i, (σ → ZMod (q i)) → FiniteProbabilityWeights (τ → ZMod (q i)))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : (τ → ZMod (q i)) → ℝ), (primeCoordinateReference (σ := τ) q i).mean f = 0 →
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f ^ 2) ≤
        C i * (primeCoordinateReference (σ := τ) q i).mean (fun y => f y ^ 2))
    (hmean : ∀ i (f : (τ → ZMod (q i)) → ℝ),
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f) =
        (primeCoordinateReference (σ := τ) q i).mean f)
    (w : (σ → ℤ) → ℝ) (f : (τ → ℤ) → ℝ) (B : ℕ) (hKB : K.card ≤ B)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ K, C i ≤ κ ^ 2)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hcopX : ∀ i ∉ K, MX.Coprime (q i)) (hcopY : ∀ i ∉ K, MY.Coprime (q i))
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card σ : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card τ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ)) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (primeCoordinateReference (σ := σ) q i)
      (primeCoordinateReference (σ := τ) q i) (kernel i) (hmean i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          productTruncatedPairing (fun i : {i // i ∉ K} => c i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤
      (2 : ℝ) ^ K.card * (κ ^ (B - K.card) *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * 3) *
        (residuePrimeCoordinateMassRatio loY NY MY aY q K baseY * 3)) := by
  have hx := residueCellOutsideDensity_norm_of_lengths (ι := ι) (σ := σ)
    loX NX MX aX q hMX hpair K baseX hcopX uX w hw B P modLog dimX hP hmodLog hcount hmoduli hdimX hlengthX
  have hy := residueCellOutsideDensity_norm_of_lengths (ι := ι) (σ := τ)
    loY NY MY aY q hMY hpair K baseY hcopY uY f hf B P modLog dimY hP hmodLog hcount hmoduli hdimY hlengthY
  exact residue_initial_conditioning_shell_s2 loX NX MX aX hneX loY NY MY aY hneY q hpair K baseX baseY uX uY
    kernel C hC hbound hmean w f B hKB hκ0 hκ1 hcap hx hy

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.residue_initial_conditioning_shell_of_lengths_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.residue_initial_conditioning_shell_of_lengths_s2_oai.{u_1, u_2, u_3}
