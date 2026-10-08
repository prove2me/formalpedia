-- Prove2me | solution 1 for OAI.Erdos3.exists_finite_cylinder_removal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:31:17.221991+00:00
-- url     : https://prove2.me/submissions/5fcb6cd2-7a91-4e79-b447-3751156a06ef

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016

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

theorem productConditionalMean_empty (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ ∅ f x = (FiniteProbabilityWeights.pi μ).mean f := by
  simp only [productConditionalMean, productCoordinateMix_empty]

theorem productConditionalMean_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => c * f y) x = c * productConditionalMean μ S f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul _ _

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

open scoped BigOperators

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

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

variable [Fintype ι] [∀ i, Fintype (X i)]

theorem mem_bounded (b : ℕ) (c : ProductCylinder X) :
    c ∈ bounded (X := X) b ↔ c.1.card ≤ b := by
  classical
  simp only [bounded, Finset.mem_filter, Finset.mem_univ, true_and]

theorem bounded_nonempty (b : ℕ) (base : ∀ i, X i) :
    (bounded (X := X) b).Nonempty := by
  exact ⟨ofAssignment ∅ base, (mem_bounded b _).mpr (by simp [ofAssignment])⟩

theorem mass_ofAssignment (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    (ofAssignment S x).mass μ base f = productConditionalMean μ S f x := by
  apply productConditionalMean_depends
  intro i hi
  change i ∈ S at hi
  change (if h : i ∈ S then x i else base i) = x i
  exact dif_pos hi

theorem mass_empty (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) :
    (ofAssignment ∅ base).mass μ base f = (FiniteProbabilityWeights.pi μ).mean f := by
  rw [mass_ofAssignment, productConditionalMean_empty]

theorem mass_mono (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    {f g : (∀ i, X i) → ℝ} (hfg : ∀ x, f x ≤ g x) (c : ProductCylinder X) :
    c.mass μ base f ≤ c.mass μ base g :=
  (FiniteProbabilityWeights.pi μ).mean_mono (fun _ => hfg _)

end ProductCylinder

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

end Erdos3

end

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

theorem exists_maximizer (K : ℝ) (b : ℕ) : ∃ c : ProductCylinder X, Maximizes μ base f K b c := by
  classical
  obtain ⟨c, hc, hm⟩ := Finset.exists_max_image (bounded (X := X) b) (score μ base f K)
    (bounded_nonempty b base)
  exact ⟨c, (mem_bounded b c).mp hc, fun d hd => hm d ((mem_bounded b d).mpr hd)⟩

variable {μ base f}

theorem Maximizes.empty_le {K : ℝ} {b : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K b c) :
    (FiniteProbabilityWeights.pi μ).mean f ≤ c.mass μ base f / K ^ c.1.card := by
  have h := hmax.2 (ofAssignment ∅ base) (by simp [ofAssignment])
  change (ofAssignment ∅ base).mass μ base f / K ^ 0 ≤ c.mass μ base f / K ^ c.1.card at h
  rw [mass_empty, pow_zero, div_one] at h
  exact h

theorem Maximizes.mass_gt {K τ : ℝ} {b : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K b c) (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hm : τ < (FiniteProbabilityWeights.pi μ).mean f) : τ < c.mass μ base f := by
  have hpos : 0 < K ^ c.1.card := pow_pos (zero_lt_one.trans_le hK) _
  have h := (lt_div_iff₀ hpos).mp (hm.trans_le hmax.empty_le)
  exact (le_mul_of_one_le_right hτ (one_le_pow₀ hK)).trans_lt h

theorem Maximizes.card_le {K τ : ℝ} {j r : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K (j + r) c) (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hm : τ < (FiniteProbabilityWeights.pi μ).mean f)
    (hcap : ∀ d : ProductCylinder X, d.1.card ≤ j + r → d.mass μ base f ≤ 2)
    (hcut : 2 ≤ τ * K ^ (j + 1)) : c.1.card ≤ j := by
  by_contra hn
  have hle : j + 1 ≤ c.1.card := by omega
  have hpos : 0 < K ^ c.1.card := pow_pos (zero_lt_one.trans_le hK) _
  have h := (lt_div_iff₀ hpos).mp (hm.trans_le hmax.empty_le)
  have hmono := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hle) hτ
  have hcap' := hcap c hmax.1
  linarith

theorem Maximizes.refinement_bound {K : ℝ} {j r : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K (j + r) c) (hK : 0 < K) (hc : c.1.card ≤ j)
    (J : Finset ι) (hdis : Disjoint c.1 J) (hJ : J.card ≤ r) (y : ∀ i, X i) :
    productConditionalMean μ (c.1 ∪ J) f y ≤ K ^ J.card * c.mass μ base f := by
  have hcard : (c.1 ∪ J).card ≤ j + r := by
    rw [Finset.card_union_of_disjoint hdis]
    omega
  have hs := hmax.2 (ofAssignment (c.1 ∪ J) y) hcard
  change (ofAssignment (c.1 ∪ J) y).mass μ base f / K ^ (c.1 ∪ J).card ≤
    c.mass μ base f / K ^ c.1.card at hs
  rw [mass_ofAssignment] at hs
  have hcross := (div_le_div_iff₀ (pow_pos hK (c.1 ∪ J).card) (pow_pos hK c.1.card)).mp hs
  apply (mul_le_mul_iff_left₀ (pow_pos hK c.1.card)).mp
  calc
    _ ≤ c.mass μ base f * K ^ (c.1 ∪ J).card := hcross
    _ = (K ^ J.card * c.mass μ base f) * K ^ c.1.card := by
      rw [Finset.card_union_of_disjoint hdis, pow_add]
      ring

end Erdos3.ProductCylinder

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

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

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

variable {μ base f}

theorem Maximizes.normalized_bounded {K : ℝ} {j r : ℕ} {c : ProductCylinder X}
    (hmax : Maximizes μ base f K (j + r) c) (hK : 1 ≤ K) (hc : c.1.card ≤ j)
    (hm : 0 < c.mass μ base f) :
    ProductBoundedMarginals μ (normalizedSection μ base f c) K r := by
  intro B hB x _
  change productConditionalMean μ B
    (fun y => (c.mass μ base f)⁻¹ * productSectionAverage μ c.1 c.1 (c.assignment base) f y) x ≤ _
  rw [productConditionalMean_smul, productConditionalMean_sectionAverage μ c.1 c.1 B (by rfl)]
  have hdis : Disjoint c.1 (B \ c.1) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 hi
  have hcard : (B \ c.1).card ≤ r := (Finset.card_le_card Finset.sdiff_subset).trans hB
  have hb := hmax.refinement_bound (zero_lt_one.trans_le hK) hc (B \ c.1) hdis hcard
    (productCoordinateMix c.1 (c.assignment base) x)
  calc
    _ ≤ (c.mass μ base f)⁻¹ * (K ^ (B \ c.1).card * c.mass μ base f) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hm.le)
    _ = K ^ (B \ c.1).card := by field_simp
    _ ≤ K ^ B.card := pow_le_pow_right₀ hK (Finset.card_le_card Finset.sdiff_subset)

theorem exists_regular {K τ : ℝ} {j r : ℕ} (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hm : τ < (FiniteProbabilityWeights.pi μ).mean f)
    (hcap : ∀ d : ProductCylinder X, d.1.card ≤ j + r → d.mass μ base f ≤ 2)
    (hcut : 2 ≤ τ * K ^ (j + 1)) :
    ∃ c : ProductCylinder X, c.1.card ≤ j ∧ τ < c.mass μ base f ∧
      ProductBoundedMarginals μ (normalizedSection μ base f c) K r := by
  obtain ⟨c, hc⟩ := exists_maximizer μ base f K (j + r)
  have hcard := hc.card_le hK hτ hm hcap hcut
  have hmass := hc.mass_gt hK hτ hm
  exact ⟨c, hcard, hmass, hc.normalized_bounded hK hcard (hτ.trans_lt hmass)⟩

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

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

theorem observedProductDensity_mono {f g : Ω → ℝ} (hfg : ∀ z, f z ≤ g z) (x : ∀ i, X i) :
    observedProductDensity μ p F f x ≤ observedProductDensity μ p F g x := by
  classical
  apply div_le_div_of_nonneg_right _ ((FiniteProbabilityWeights.pi μ).nonneg x)
  apply p.mean_mono
  intro z
  split_ifs
  · exact hfg z
  · exact le_rfl

theorem observedProductDensity_add (f g : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (fun z => f z + g z) x =
      observedProductDensity μ p F f x + observedProductDensity μ p F g x := by
  classical
  have he : p.fiberMean F x (fun z => f z + g z) = p.fiberMean F x f + p.fiberMean F x g := by
    unfold FiniteProbabilityWeights.fiberMean
    rw [← p.mean_add]
    congr 1
    funext z
    split_ifs <;> simp
  change p.fiberMean F x (fun z => f z + g z) / _ = p.fiberMean F x f / _ + p.fiberMean F x g / _
  rw [he, add_div]

theorem observedProductDensity_mean (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean (observedProductDensity μ p F f) = p.mean f := by
  have h := observedProductDensity_conditional μ hμ p F f ∅ base
  rw [productConditionalMean_empty, productFiberMass_empty, (FiniteProbabilityWeights.pi μ).total,
    div_one] at h
  simpa [productFiberIndicator] using h

theorem observedProductDensity_marginal_le (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (hf : ∀ z, f z ≤ 1) {η : ℝ} {r : ℕ}
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η r)
    (S : Finset ι) (hS : S.card ≤ r) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ p F f) x ≤ 1 + η := by
  have hm : productConditionalMean μ S (observedProductDensity μ p F f) x ≤
      productConditionalMean μ S (observedProductDensity μ p F (fun _ => 1)) x :=
    (FiniteProbabilityWeights.pi μ).mean_mono
      (fun y => observedProductDensity_mono μ p F hf (productCoordinateMix S x y))
  have hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0 :=
    (Finset.prod_pos (fun i _ => hμ i (x i))).ne'
  have hb := (abs_le.mp (hbase S hS x hx)).2
  linarith

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

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

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

theorem cut_add_erase (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) :
    c.cut F w z + c.erase F w z = w z := by
  unfold cut erase
  split_ifs <;> simp

theorem erase_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.erase F w z := by
  unfold erase
  split_ifs <;> simp [hw]

theorem erase_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.erase F w z ≤ w z := by
  unfold erase
  split_ifs <;> simp [hw]

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

theorem density_erase (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.erase F w) x =
      if c.Contains x then 0 else observedProductDensity μ p F w x := by
  classical
  have he : (fun z => c.cut F w z + c.erase F w z) = w := funext (c.cut_add_erase F w)
  have hs := observedProductDensity_add μ p F (c.cut F w) (c.erase F w) x
  rw [he, c.density_cut] at hs
  by_cases hx : c.Contains x
  · rw [if_pos hx] at hs ⊢
    linarith
  · rw [if_neg hx] at hs ⊢
    linarith

theorem mass_erase_self (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    c.mass μ base (observedProductDensity μ p F (c.erase F w)) = 0 := by
  have hc (y : ∀ i, X i) : c.Contains (productCoordinateMix c.1 (c.assignment base) y) := by
    intro i
    simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property
  change (FiniteProbabilityWeights.pi μ).mean
    (fun y => observedProductDensity μ p F (c.erase F w) (productCoordinateMix c.1 (c.assignment base) y)) = 0
  have he : (fun y => observedProductDensity μ p F (c.erase F w)
      (productCoordinateMix c.1 (c.assignment base) y)) = (fun _ => 0) := by
    funext y
    rw [c.density_erase, if_pos (hc y)]
  rw [he, FiniteProbabilityWeights.mean_const]

omit [∀ i, DecidableEq (X i)] in
theorem mass_erase_le (c d : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) :
    d.mass μ base (observedProductDensity μ p F (c.erase F w)) ≤
      d.mass μ base (observedProductDensity μ p F w) :=
  mass_mono μ base (observedProductDensity_mono μ p F (c.erase_le F w hw)) d

end Erdos3.ProductCylinder

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

theorem mem_positiveCandidates (b : ℕ) (w : Ω → ℝ) (c : ProductCylinder X) :
    c ∈ positiveCandidates μ base p F b w ↔
      c.1.card ≤ b ∧ 0 < c.mass μ base (observedProductDensity μ p F w) := by
  classical
  simp only [positiveCandidates, Finset.mem_filter, mem_bounded]

theorem positiveCandidates_card_le (b : ℕ) (w : Ω → ℝ) :
    (positiveCandidates μ base p F b w).card ≤ (bounded (X := X) b).card := by
  classical
  exact Finset.card_filter_le _ _

theorem positiveCandidates_erase_card_lt [∀ i, DecidableEq (X i)] (b : ℕ) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (c : ProductCylinder X) (hc : c.1.card ≤ b)
    (hm : 0 < c.mass μ base (observedProductDensity μ p F w)) :
    (positiveCandidates μ base p F b (c.erase F w)).card <
      (positiveCandidates μ base p F b w).card := by
  classical
  have hsub : positiveCandidates μ base p F b (c.erase F w) ⊆
      (positiveCandidates μ base p F b w).erase c := by
    intro d hd
    obtain ⟨hdsize, hdmass⟩ := (mem_positiveCandidates μ base p F b (c.erase F w) d).mp hd
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      subst d
      rw [c.mass_erase_self] at hdmass
      exact (lt_irrefl 0) hdmass
    · exact (mem_positiveCandidates μ base p F b w d).mpr
        ⟨hdsize, hdmass.trans_le (c.mass_erase_le d μ base p F w hw)⟩
  have hcpos := (mem_positiveCandidates μ base p F b w c).mpr ⟨hc, hm⟩
  exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hcpos)

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} {X : ι → Type*}

end Erdos3

end

section

namespace Erdos3

open ProductCylinder

theorem exists_finite_cylinder_removal {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (K τ η : ℝ) (j r : ℕ) (hK : 1 ≤ K) (hτ : 0 ≤ τ) (hη : η ≤ 1)
    (hcut : 2 ≤ τ * K ^ (j + 1))
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r))
    (w : Ω → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    ∃ (v : Ω → ℝ) (cs : List (ProductCylinder X)),
      CylinderRemovalChain μ base p F K τ j r w v cs ∧
      cs.length ≤ (ProductCylinder.bounded (X := X) (j + r)).card ∧ p.mean v ≤ τ ∧
      (∀ z, 0 ≤ v z ∧ v z ≤ 1) := by
  have aux : ∀ n : ℕ, ∀ w : Ω → ℝ, (∀ z, 0 ≤ w z) → (∀ z, w z ≤ 1) →
      (positiveCandidates μ base p F (j + r) w).card ≤ n →
      ∃ (v : Ω → ℝ) (cs : List (ProductCylinder X)),
        CylinderRemovalChain μ base p F K τ j r w v cs ∧ cs.length ≤ n ∧ p.mean v ≤ τ ∧
        (∀ z, 0 ≤ v z ∧ v z ≤ 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw0 hw1 hn
      by_cases hs : p.mean w ≤ τ
      · exact ⟨w, [], .nil w, by simp, hs, fun z => ⟨hw0 z, hw1 z⟩⟩
      · have hm : τ < (FiniteProbabilityWeights.pi μ).mean (observedProductDensity μ p F w) := by
          rw [observedProductDensity_mean μ p F hμ w base]
          exact lt_of_not_ge hs
        have hcap : ∀ d : ProductCylinder X, d.1.card ≤ j + r →
            d.mass μ base (observedProductDensity μ p F w) ≤ 2 := by
          intro d hd
          have hb := observedProductDensity_marginal_le μ p F hμ w hw1 hbase d.1 hd (d.assignment base)
          change productConditionalMean μ d.1 (observedProductDensity μ p F w) (d.assignment base) ≤ 2
          linarith
        obtain ⟨c, hc, hmass, hregular⟩ := ProductCylinder.exists_regular hK hτ hm hcap hcut
        have hpos : 0 < c.mass μ base (observedProductDensity μ p F w) := hτ.trans_lt hmass
        have hsize : c.1.card ≤ j + r := by omega
        have hlt := positiveCandidates_erase_card_lt μ base p F (j + r) w hw0 c hsize hpos
        have hnext : (positiveCandidates μ base p F (j + r) (c.erase F w)).card < n := hlt.trans_le hn
        obtain ⟨v, cs, hchain, hcs, hv, hvbounds⟩ := ih _ hnext (c.erase F w)
          (c.erase_nonneg F w hw0) (fun z => (c.erase_le F w hw0 z).trans (hw1 z)) le_rfl
        refine ⟨v, c :: cs, .cons c hc hmass hregular hchain, ?_, hv, hvbounds⟩
        simp only [List.length_cons]
        omega
  exact aux _ w hw0 hw1 (positiveCandidates_card_le μ base p F (j + r) w)

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.exists_finite_cylinder_removal.{u_1, u_2, u_3} := @OAI.Erdos3.exists_finite_cylinder_removal.{u_1, u_2, u_3}
