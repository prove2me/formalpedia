-- Prove2me | solution 1 for OAI.Erdos3.productCouplingPairing_conditioning_error_le_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:26:15.279331+00:00
-- url     : https://prove2.me/submissions/12fe0280-4a07-4a5d-b820-025529f313af

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B138
import Definitions.Def_OAIE3v2B139

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem productCoordinateMix_comp (S T : Finset I) (x y z : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix S x y) z =
      productCoordinateMix (S ∩ T) x (productCoordinateMix T y z) := by
  funext i
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
    simp [productCoordinateMix, hs, ht]

theorem productCoordinateMix_left (S : Finset I) (x y z : ∀ i, X i) :
    productCoordinateMix S (productCoordinateMix S x y) z = productCoordinateMix S x z := by
  funext i
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi]

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

open scoped BigOperators Classical

theorem productFiberIndicator_depends {I : Type*} {X : I → Type*}
    (S : Finset I) (x : ∀ i, X i) : ProductDependsOn S (productFiberIndicator S x) := by
  intro y z hyz
  have he : (∀ i ∈ S, y i = x i) ↔ (∀ i ∈ S, z i = x i) :=
    ⟨fun h i hi => (hyz i hi).symm.trans (h i hi),
      fun h i hi => (hyz i hi).trans (h i hi)⟩
  simp only [productFiberIndicator, he]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DisjointPowersetSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I]

theorem disjoint_powerset_sum (T U : Finset I) (hTU : Disjoint T U) (f : Finset I → ℝ) :
    (∑ C ∈ (T ∪ U).powerset, f C) = ∑ A ∈ T.powerset, ∑ B ∈ U.powerset, f (A ∪ B) := by
  rw [← Finset.sum_product T.powerset U.powerset (fun p : Finset I × Finset I => f (p.1 ∪ p.2))]
  apply Finset.sum_bij' (fun C _ => (C ∩ T, C ∩ U)) (fun p _ => p.1 ∪ p.2)
  · intro C _
    exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
      Finset.mem_powerset.mpr Finset.inter_subset_right⟩
  · intro p hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    exact Finset.mem_powerset.mpr (Finset.union_subset_union
      (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB))
  · intro C hC
    have hsub := Finset.mem_powerset.mp hC
    ext i
    have hi : i ∈ C → i ∈ T ∨ i ∈ U := fun h => Finset.mem_union.mp (hsub h)
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  · intro p hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    have hAsub := Finset.mem_powerset.mp hA
    have hBsub := Finset.mem_powerset.mp hB
    apply Prod.ext <;> ext i
    · have hAi : i ∈ p.1 → i ∈ T := fun h => hAsub h
      have hBi : i ∈ p.2 → i ∈ U := fun h => hBsub h
      have hdis : ¬(i ∈ T ∧ i ∈ U) := fun h => Finset.disjoint_left.mp hTU h.1 h.2
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    · have hAi : i ∈ p.1 → i ∈ T := fun h => hAsub h
      have hBi : i ∈ p.2 → i ∈ U := fun h => hBsub h
      have hdis : ¬(i ∈ T ∧ i ∈ U) := fun h => Finset.disjoint_left.mp hTU h.1 h.2
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
  · intro C hC
    congr 1
    have hsub := Finset.mem_powerset.mp hC
    ext i
    have hi : i ∈ C → i ∈ T ∨ i ∈ U := fun h => Finset.mem_union.mp (hsub h)
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentProductMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMean_mul_disjoint (S T : Finset ι) (hST : Disjoint S T)
    (f g : (∀ i, X i) → ℝ) (hf : ProductDependsOn S f) (hg : ProductDependsOn T g) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * g x) =
      (FiniteProbabilityWeights.pi μ).mean f * (FiniteProbabilityWeights.pi μ).mean g := by
  have hleft (x y : ∀ i, X i) : f (productCoordinateMix S x y) = f x := by
    apply hf
    intro i hi
    simp only [productCoordinateMix, hi, ite_true]
  have hright (x y : ∀ i, X i) : g (productCoordinateMix S x y) = g y := by
    apply hg
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hST hs hi
    simp only [productCoordinateMix, hn, ite_false]
  rw [← productMean_coordinateMix μ S (fun x => f x * g x)]
  simp only [hleft, hright, FiniteProbabilityWeights.mean_const_mul, FiniteProbabilityWeights.mean_mul_const]

theorem productConditionalMean_mul_disjoint (S T R : Finset ι) (hST : Disjoint S T)
    (f g : (∀ i, X i) → ℝ) (hf : ProductDependsOn S f) (hg : ProductDependsOn T g) (x : ∀ i, X i) :
    productConditionalMean μ R (fun y => f y * g y) x =
      productConditionalMean μ R f x * productConditionalMean μ R g x := by
  have hdep (U : Finset ι) (h : (∀ i, X i) → ℝ) (hh : ProductDependsOn U h) :
      ProductDependsOn U (fun y => h (productCoordinateMix R x y)) := by
    intro y z hyz
    apply hh
    intro i hi
    by_cases hr : i ∈ R
    · simp only [productCoordinateMix, hr, ite_true]
    · simp only [productCoordinateMix, hr, ite_false, hyz i hi]
  exact productMean_mul_disjoint μ S T hST _ _ (hdep S f hf) (hdep T g hg)

theorem productConditionalMean_union_irrelevant (S R T : Finset ι) (hST : Disjoint S T)
    (f : (∀ i, X i) → ℝ) (hf : ProductDependsOn S f) (x : ∀ i, X i) :
    productConditionalMean μ (R ∪ T) f x = productConditionalMean μ R f x := by
  unfold productConditionalMean
  congr 1
  funext y
  apply hf
  intro i hi
  have hn : i ∉ T := fun ht => Finset.disjoint_left.mp hST hi ht
  simp only [productCoordinateMix, Finset.mem_union, hn, or_false]

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

theorem productSectionAverage_depends (T A : Finset I) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) : ProductDependsOn Tᶜ (productSectionAverage μ T A z f) := by
  intro x y hxy
  unfold productSectionAverage
  congr 1
  funext v
  congr 1
  funext i
  by_cases hi : i ∈ T
  · simp only [productCoordinateMix, hi, ite_true]
  · have he := hxy i (by simpa only [Finset.mem_compl] using hi)
    simp only [productCoordinateMix, hi, ite_false, he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_self (I : Finset ι) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ I I z f x = f (productCoordinateMix I z x) := by
  simp only [productSectionAverage, productCoordinateMix_left, FiniteProbabilityWeights.mean_const]

theorem productFiberIndicator_mul_section (I : Finset ι) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    (fun x => productFiberIndicator I z x * productSectionAverage μ I I z f x) =
      (fun x => productFiberIndicator I z x * f x) := by
  funext x
  rw [productSectionAverage_self]
  by_cases hx : ∀ i ∈ I, x i = z i
  · have he : productCoordinateMix I z x = x := by
      funext i
      by_cases hi : i ∈ I
      · simp only [productCoordinateMix, hi, ite_true, hx i hi]
      · simp only [productCoordinateMix, hi, ite_false]
    rw [he]
  · simp only [productFiberIndicator, hx, ite_false, zero_mul]

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

theorem productANOVA_inclusion_exclusion (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productANOVA μ S f x = ∑ T ∈ S.powerset,
      (-1 : ℝ) ^ (S.card - T.card) * productConditionalMean μ T f x := by
  unfold productANOVA
  apply Finset.sum_bij' (fun U _ => S \ U) (fun T _ => S \ T)
  · intro U _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro T _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro U hU
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hU)
  · intro T hT
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT)
  · intro U hU
    have hu := Finset.mem_powerset.mp hU
    have hc : S.card - (S \ U).card = U.card := by
      rw [Finset.card_sdiff_of_subset hu]
      exact Nat.sub_sub_self (Finset.card_le_card hu)
    rw [hc]

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_mul_blocks (I J A B : Finset ι) (hIJ : Disjoint I J)
    (hAI : A ⊆ I) (hBJ : B ⊆ J) (f g : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn I f) (hg : ProductDependsOn J g) (x : ∀ i, X i) :
    productANOVA μ (A ∪ B) (fun y => f y * g y) x = productANOVA μ A f x * productANOVA μ B g x := by
  have hAB := hIJ.mono hAI hBJ
  simp only [productANOVA_inclusion_exclusion]
  rw [disjoint_powerset_sum A B hAB]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hUA := Finset.mem_powerset.mp hU
  have hVB := Finset.mem_powerset.mp hV
  have hUV := hAB.mono hUA hVB
  rw [productConditionalMean_mul_disjoint μ I J (U ∪ V) hIJ f g hf hg x,
    productConditionalMean_union_irrelevant μ I U V (hIJ.mono_right (hVB.trans hBJ)) f hf x]
  have he := productConditionalMean_union_irrelevant μ J V U
    (hIJ.symm.mono_right (hUA.trans hAI)) g hg x
  rw [Finset.union_comm] at he
  rw [he]
  have hc : (A ∪ B).card - (U ∪ V).card = (A.card - U.card) + (B.card - V.card) := by
    rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hUV]
    have := Finset.card_le_card hUA
    have := Finset.card_le_card hVB
    omega
  rw [hc, pow_add]
  ring

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

theorem productANOVAEnergy_le_mean_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (D : Finset (Finset ι)) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f ≤ (FiniteProbabilityWeights.pi μ).mean (fun x => f x ^ 2) := by
  have hcs := (FiniteProbabilityWeights.pi μ).mean_mul_sq_le f (productANOVATruncation μ D f)
  rw [productANOVAEnergy_square, ← productANOVAEnergy_pairing] at hcs
  by_cases hz : productANOVAEnergy μ D f = 0
  · rw [hz]
    exact FiniteProbabilityWeights.mean_nonneg _ (fun x => sq_nonneg (f x))
  · have hp : 0 < productANOVAEnergy μ D f :=
      lt_of_le_of_ne (productANOVAEnergy_nonneg μ D f) (Ne.symm hz)
    rw [pow_two] at hcs
    exact le_of_mul_le_mul_right hcs hp

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

theorem productANOVATruncation_of_depends (S : Finset ι) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn S f) : productANOVATruncation μ S.powerset f = f := by
  funext x
  exact (productANOVA_reconstruct μ S f x).trans (productConditionalMean_of_depends μ S hf x)

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

theorem productCoupling_left_mean (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean (fun z => f (fun i => (z i).1)) =
      (FiniteProbabilityWeights.pi μ).mean f :=
  productMean_coordinate_transport _ μ (fun _ => Prod.fst) (fun i => (c i).left_mean) f

theorem productCouplingPairing_sq_le (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c f g ^ 2 ≤
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x ^ 2) *
      (FiniteProbabilityWeights.pi ν).mean (fun y => g y ^ 2) := by
  have h := (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean_mul_sq_le
    (fun z => f (fun i => (z i).1)) (fun z => g (fun i => (z i).2))
  rw [productCoupling_left_mean c (fun x => f x ^ 2),
    productCoupling_right_mean c (fun y => g y ^ 2)] at h
  exact h

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

theorem ProductDependsOn.coordinateMap {ι : Type*} {X Y : ι → Type*} {S : Finset ι}
    {f : (∀ i, Y i) → ℝ} (hf : ProductDependsOn S f) (F : ∀ i, X i → Y i) :
    ProductDependsOn S (fun x => f (fun i => F i (x i))) := by
  intro x y hxy
  exact hf _ _ (fun i hi => congrArg (F i) (hxy i hi))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_blocks (I J : Finset ι) (hIJ : Disjoint I J)
    (u v : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ)
    (hu : ProductDependsOn I u) (hv : ProductDependsOn J v)
    (hf : ProductDependsOn I f) (hg : ProductDependsOn J g) :
    productCouplingPairing c (fun x => u x * v x) (fun y => f y * g y) =
      productCouplingPairing c u f * productCouplingPairing c v g := by
  have hl : ProductDependsOn I (fun z : ∀ i, X i × Y i => u (fun i => (z i).1) * f (fun i => (z i).2)) := by
    simpa only [Finset.union_self] using (hu.coordinateMap (fun _ => Prod.fst)).mul
      (hf.coordinateMap (fun _ => Prod.snd))
  have hr : ProductDependsOn J (fun z : ∀ i, X i × Y i => v (fun i => (z i).1) * g (fun i => (z i).2)) := by
    simpa only [Finset.union_self] using (hv.coordinateMap (fun _ => Prod.fst)).mul
      (hg.coordinateMap (fun _ => Prod.snd))
  calc
    _ = (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean
        (fun z => (u (fun i => (z i).1) * f (fun i => (z i).2)) *
          (v (fun i => (z i).1) * g (fun i => (z i).2))) := by
      unfold productCouplingPairing
      congr 1
      funext z
      ring
    _ = _ := productMean_mul_disjoint _ I J hIJ _ _ hl hr

theorem productCouplingPairing_ANOVA_blocks (I J A B : Finset ι) (hIJ : Disjoint I J)
    (hAI : A ⊆ I) (hBJ : B ⊆ J)
    (u v : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ)
    (hu : ProductDependsOn I u) (hv : ProductDependsOn J v)
    (hf : ProductDependsOn I f) (hg : ProductDependsOn J g) :
    productCouplingPairing c (productANOVA μ (A ∪ B) (fun x => u x * v x))
      (productANOVA ν (A ∪ B) (fun y => f y * g y)) =
      productCouplingPairing c (productANOVA μ A u) (productANOVA ν A f) *
        productCouplingPairing c (productANOVA μ B v) (productANOVA ν B g) := by
  have hx := funext (productANOVA_mul_blocks μ I J A B hIJ hAI hBJ u v hu hv)
  have hy := funext (productANOVA_mul_blocks ν I J A B hIJ hAI hBJ f g hf hg)
  rw [hx, hy]
  exact productCouplingPairing_blocks c A B (hIJ.mono hAI hBJ) _ _ _ _
    (productANOVA_depends μ A u) (productANOVA_depends μ B v)
    (productANOVA_depends ν A f) (productANOVA_depends ν B g)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AtomSupportBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productFiberIndicator_sq_mean_le_one (μ : ∀ i, FiniteProbabilityWeights (X i))
    (I : Finset ι) (x : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean (fun z => productFiberIndicator I x z ^ 2) ≤ 1 := by
  apply (FiniteProbabilityWeights.mean_mono _ (g := fun _ => (1 : ℝ)) _).trans_eq
    (FiniteProbabilityWeights.mean_const _ 1)
  intro z
  unfold productFiberIndicator
  split_ifs <;> norm_num

theorem productCouplingPairing_atom_component_le_one
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
    (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i)) (I A : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) :
    |productCouplingPairing c (productANOVA μ A (productFiberIndicator I x))
      (productANOVA ν A (productFiberIndicator I y))| ≤ 1 := by
  have hx := (productANOVAEnergy_le_mean_sq μ {A} (productFiberIndicator I x)).trans
    (productFiberIndicator_sq_mean_le_one μ I x)
  have hy := (productANOVAEnergy_le_mean_sq ν {A} (productFiberIndicator I y)).trans
    (productFiberIndicator_sq_mean_le_one ν I y)
  simp only [productANOVAEnergy, Finset.sum_singleton] at hx hy
  have hc := productCouplingPairing_sq_le c (productANOVA μ A (productFiberIndicator I x))
    (productANOVA ν A (productFiberIndicator I y))
  have hb := hc.trans ((mul_le_of_le_one_left
    (FiniteProbabilityWeights.mean_nonneg _ (fun z => sq_nonneg (productANOVA ν A (productFiberIndicator I y) z))) hx).trans hy)
  apply (sq_le_sq₀ (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)).mp
  simpa only [sq_abs, one_pow] using hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportCutoffSplit
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_support_cutoff_split (I : Finset ι) (b : ℕ) (F : Finset ι → ℝ) :
    (∑ S ∈ lowDegreeCoordinateSets ι b, F S) =
      ∑ A ∈ I.powerset, ∑ B ∈ Iᶜ.powerset, if A.card + B.card ≤ b then F (A ∪ B) else 0 := by
  have he : lowDegreeCoordinateSets ι b = Finset.univ.powerset.filter (fun S => S.card ≤ b) := by
    ext S
    simp only [mem_lowDegreeCoordinateSets, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
  rw [he, Finset.sum_filter]
  have hu : (Finset.univ : Finset ι) = I ∪ Iᶜ := (Finset.union_compl I).symm
  rw [hu, disjoint_powerset_sum I Iᶜ disjoint_compl_right]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  have hd : Disjoint A B := disjoint_compl_right.mono
    (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)
  rw [Finset.card_union_of_disjoint hd]

theorem sum_cutoff_core_shell (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    (a v : Finset ι → ℝ) :
    (∑ A ∈ I.powerset, ∑ B ∈ Iᶜ.powerset, if A.card + B.card ≤ b then a A * v B else 0) =
      (∑ A ∈ I.powerset, a A) * (∑ B ∈ Iᶜ.powerset, if B.card ≤ b - I.card then v B else 0) +
      ∑ A ∈ I.powerset, a A *
        (∑ B ∈ Iᶜ.powerset, if b - I.card < B.card ∧ A.card + B.card ≤ b then v B else 0) := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B _
  have hAcard := Finset.card_le_card (Finset.mem_powerset.mp hA)
  by_cases hc : B.card ≤ b - I.card
  · have hab : A.card + B.card ≤ b := by omega
    have hn : ¬ b - I.card < B.card := by omega
    simp only [hc, hab, hn, false_and, ite_true, ite_false, mul_zero, add_zero]
  · have hgt : b - I.card < B.card := by omega
    by_cases hab : A.card + B.card ≤ b <;>
      simp only [hc, hgt, hab, true_and, ite_true, ite_false, mul_zero, zero_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConditioningShellError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_cutoff_blocks (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    (u v : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ)
    (hu : ProductDependsOn I u) (hv : ProductDependsOn Iᶜ v)
    (hf : ProductDependsOn I f) (hg : ProductDependsOn Iᶜ g) :
    productCouplingPairing c (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun x => u x * v x))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun y => f y * g y)) =
      productCouplingPairing c u f * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) v)
        (productANOVATruncation ν (conditioningCoreSupports I b) g) +
      ∑ A ∈ I.powerset, productCouplingPairing c (productANOVA μ A u) (productANOVA ν A f) *
        productCouplingPairing c (productANOVATruncation μ (conditioningShellSupports I A b) v)
          (productANOVATruncation ν (conditioningShellSupports I A b) g) := by
  let α := fun A => productCouplingPairing c (productANOVA μ A u) (productANOVA ν A f)
  let β := fun B => productCouplingPairing c (productANOVA μ B v) (productANOVA ν B g)
  have hinside : (∑ A ∈ I.powerset, α A) = productCouplingPairing c u f := by
    dsimp only [α]
    rw [← productCouplingPairing_truncation,
      productANOVATruncation_of_depends μ I u hu, productANOVATruncation_of_depends ν I f hf]
  calc
    _ = ∑ A ∈ I.powerset, ∑ B ∈ Iᶜ.powerset, if A.card + B.card ≤ b then α A * β B else 0 := by
      rw [productCouplingPairing_truncation, sum_support_cutoff_split I b]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro B hB
      split_ifs
      · exact productCouplingPairing_ANOVA_blocks c I Iᶜ A B disjoint_compl_right
          (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB) u v f g hu hv hf hg
      · rfl
    _ = (∑ A ∈ I.powerset, α A) * (∑ B ∈ Iᶜ.powerset, if B.card ≤ b - I.card then β B else 0) +
        ∑ A ∈ I.powerset, α A *
          (∑ B ∈ Iᶜ.powerset, if b - I.card < B.card ∧ A.card + B.card ≤ b then β B else 0) :=
      sum_cutoff_core_shell I b hIb α β
    _ = _ := by
      rw [hinside]
      simp only [productCouplingPairing_truncation, conditioningCoreSupports, conditioningShellSupports,
        Finset.sum_filter, α, β]

theorem productCouplingPairing_cutoff_atom (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) =
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f)) +
      ∑ A ∈ I.powerset, productCouplingPairing c (productANOVA μ A (productFiberIndicator I x))
        (productANOVA ν A (productFiberIndicator I y)) * productCouplingPairing c
          (productANOVATruncation μ (conditioningShellSupports I A b) (productSectionAverage μ I I x w))
          (productANOVATruncation ν (conditioningShellSupports I A b) (productSectionAverage ν I I y f)) := by
  have h := productCouplingPairing_cutoff_blocks c I b hIb (productFiberIndicator I x)
    (productSectionAverage μ I I x w) (productFiberIndicator I y) (productSectionAverage ν I I y f)
    (productFiberIndicator_depends I x) (productSectionAverage_depends μ I I x w)
    (productFiberIndicator_depends I y) (productSectionAverage_depends ν I I y f)
  simpa only [productFiberIndicator_mul_section, productCouplingPairing_indicators] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_conditioning_error_le_s2_oai (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    {E : ℝ}
    (hshell : ∀ A ∈ I.powerset, |productCouplingPairing c
      (productANOVATruncation μ (conditioningShellSupports I A b) (productSectionAverage μ I I x w))
      (productANOVATruncation ν (conditioningShellSupports I A b) (productSectionAverage ν I I y f))| ≤ E) :
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * E := by
  rw [productCouplingPairing_cutoff_atom c I b hIb x y w f, add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _A ∈ I.powerset, E := by
      apply Finset.sum_le_sum
      intro A hA
      rw [abs_mul]
      exact (mul_le_mul (productCouplingPairing_atom_component_le_one c I A x y)
        (hshell A hA) (abs_nonneg _) zero_le_one).trans_eq (one_mul E)
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.productCouplingPairing_conditioning_error_le_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.productCouplingPairing_conditioning_error_le_s2_oai.{u_1, u_2, u_3}
