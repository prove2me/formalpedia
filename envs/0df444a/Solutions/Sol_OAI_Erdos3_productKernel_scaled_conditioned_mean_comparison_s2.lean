-- Prove2me | solution 1 for OAI.Erdos3.productKernel_scaled_conditioned_mean_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:28:34.345586+00:00
-- url     : https://prove2.me/submissions/4a2f4d5c-e2c6-4199-9c26-f93cb7434b60

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B150
import Theorems.Thm_OAI_Erdos3_productCouplingPairing_conditioning_error_le_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_dependent_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M]
    (F : (∀ i, X i) → M) :
    (∑ x, F x) = ∑ a : X 0, ∑ y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    _ = ∑ p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := Fintype.sum_prod_type _

namespace FiniteProbabilityWeights

theorem complexMean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteProbabilityWeights (X i))
    (F : (∀ i, X i) → ℂ) :
    (pi p).complexMean F = (p 0).complexMean (fun a =>
      (pi (fun i : Fin n => p i.succ)).complexMean (fun y => F (Fin.cons a y))) := by
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * F x) =
    ∑ a, ((p 0).weight a : ℂ) *
      (∑ y, ((∏ i : Fin n, (p i.succ).weight (y i) : ℝ) : ℂ) * F (Fin.cons a y))
  rw [sum_dependent_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

end FiniteProbabilityWeights

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

omit [DecidableEq ι] in
theorem mem_restrictedDegreeSupports (J S : Finset ι) (b : ℕ) :
    S ∈ restrictedDegreeSupports J b ↔ S ⊆ J ∧ S.card ≤ b := by
  simp only [restrictedDegreeSupports, Finset.mem_filter, Finset.mem_powerset]

omit [DecidableEq ι] in
theorem mem_degreeTailSupports (J S : Finset ι) (r b : ℕ) :
    S ∈ degreeTailSupports J r b ↔ S ⊆ J ∧ r < S.card ∧ S.card ≤ b := by
  simp only [degreeTailSupports, Finset.mem_filter, Finset.mem_powerset]

theorem restrictedDegreeSupports_eq_biUnion (J : Finset ι) (b : ℕ) :
    restrictedDegreeSupports J b = (Finset.range (b + 1)).biUnion (fun k => J.powersetCard k) := by
  ext S
  simp only [mem_restrictedDegreeSupports, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hS, hb⟩
    exact ⟨S.card, by omega, hS, rfl⟩
  · rintro ⟨k, hk, hS, he⟩
    exact ⟨hS, by omega⟩

theorem sum_restrictedDegreeSupports (J : Finset ι) (b : ℕ) (F : Finset ι → ℝ) :
    (∑ S ∈ restrictedDegreeSupports J b, F S) =
      ∑ k ∈ Finset.range (b + 1), ∑ S ∈ J.powersetCard k, F S := by
  rw [restrictedDegreeSupports_eq_biUnion, Finset.sum_biUnion]
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro S hSi hSj
  exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans (Finset.mem_powersetCard.mp hSj).2)

theorem sum_restrictedDegreeSupports_zero (J : Finset ι) (r : ℕ) (F : Finset ι → ℝ) :
    (∑ S ∈ restrictedDegreeSupports J r, F S) =
      F ∅ + ∑ k ∈ Finset.range r, ∑ S ∈ J.powersetCard (k + 1), F S := by
  rw [sum_restrictedDegreeSupports, Finset.sum_range_succ']
  simp only [Finset.powersetCard_zero, Finset.sum_singleton, add_comm]

theorem sum_restrictedDegreeSupports_split (J : Finset ι) {r b : ℕ} (hrb : r ≤ b)
    (F : Finset ι → ℝ) :
    (∑ S ∈ restrictedDegreeSupports J b, F S) =
      (∑ S ∈ restrictedDegreeSupports J r, F S) + (∑ S ∈ degreeTailSupports J r b, F S) := by
  have he : restrictedDegreeSupports J b = restrictedDegreeSupports J r ∪ degreeTailSupports J r b := by
    ext S
    simp only [Finset.mem_union, mem_restrictedDegreeSupports, mem_degreeTailSupports]
    constructor
    · rintro ⟨hS, hb⟩
      by_cases hr : S.card ≤ r
      · exact Or.inl ⟨hS, hr⟩
      · exact Or.inr ⟨hS, by omega, hb⟩
    · rintro (⟨hS, hr⟩ | ⟨hS, _, hb⟩)
      · exact ⟨hS, hr.trans hrb⟩
      · exact ⟨hS, hb⟩
  rw [he]
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro S hlow htail
  have hl := (mem_restrictedDegreeSupports J S r).mp hlow
  have ht := (mem_degreeTailSupports J S r b).mp htail
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_self (I : Finset ι) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ I I z f x = f (productCoordinateMix I z x) := by
  simp only [productSectionAverage, productCoordinateMix_left, FiniteProbabilityWeights.mean_const]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_smul (T A : Finset I) (z : ∀ i, X i) (c : ℝ)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z (fun y => c * f y) x = c * productSectionAverage μ T A z f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul c _

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_self_mean (I : Finset ι) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ I I z f) =
      productConditionalMean μ I f z := by
  simp only [show productSectionAverage μ I I z f =
    (fun x => f (productCoordinateMix I z x)) from funext (productSectionAverage_self μ I z f)]
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

theorem productANOVA_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : ι → Type*} [∀ i, Fintype (Y i)] (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) (x : ∀ i, Y i) :
    productANOVA ν S (productANOVA ν S f) x = productANOVA ν S f x := by
  rw [productANOVA, Finset.sum_eq_single ∅]
  · simp only [Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty,
      productConditionalMean_ANOVA, Finset.Subset.refl, ite_true]
  · intro U hU hne
    have hUS := Finset.mem_powerset.mp hU
    have hn : ¬ S ⊆ S \ U := by
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      intro h
      exact (Finset.mem_sdiff.mp (h (hUS hi))).2 hi
    simp only [productConditionalMean_ANOVA, hn, ite_false, mul_zero]
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

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVAEnergy_mono {D E : Finset (Finset I)} (hDE : D ⊆ E)
    (f : (∀ i, X i) → ℝ) : productANOVAEnergy μ D f ≤ productANOVAEnergy μ E f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hDE
  intro U _ _
  exact (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => sq_nonneg _)

theorem productANOVAEnergy_le_level (D : Finset (Finset I)) (d : ℕ)
    (hD : ∀ U ∈ D, U.card = d) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f ≤ productANOVAEnergy μ (Finset.univ.powersetCard d) f := by
  apply productANOVAEnergy_mono μ _ f
  intro U hU
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hD U hU⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteCenteredKernel
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] in
theorem centeredKernelMatrix_apply (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y) (f : Y → ℝ) (x : X) :
    (∑ y, centeredKernelMatrix ν K x y * f y) = (K x).mean f - ν.mean f := by
  simp only [centeredKernelMatrix, sub_mul, Finset.sum_sub_distrib, FiniteProbabilityWeights.mean]

theorem FiniteProbabilityWeights.mean_centered_sq (ν : FiniteProbabilityWeights Y) (f : Y → ℝ) :
    ν.mean (fun y => (f y - ν.mean f) ^ 2) = ν.mean (fun y => f y ^ 2) - (ν.mean f) ^ 2 := by
  calc
    _ = ν.mean (fun y => f y ^ 2 - (2 * ν.mean f) * f y + (ν.mean f) ^ 2) := by
      congr 1
      funext y
      ring
    _ = _ := by
      rw [ν.mean_add, ν.mean_sub, ν.mean_const_mul, ν.mean_const]
      ring

theorem centeredKernelMatrix_sq_le (μ : FiniteProbabilityWeights X) (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f : Y → ℝ, ν.mean f = 0 →
      μ.mean (fun x => (K x).mean f ^ 2) ≤ C * ν.mean (fun y => f y ^ 2)) (f : Y → ℝ) :
    μ.mean (fun x => (∑ y, centeredKernelMatrix ν K x y * f y) ^ 2) ≤
      C * ν.mean (fun y => f y ^ 2) := by
  have hzero : ν.mean (fun y => f y - ν.mean f) = 0 := by
    rw [ν.mean_sub, ν.mean_const, sub_self]
  have hc := hbound (fun y => f y - ν.mean f) hzero
  have he (x : X) : (K x).mean (fun y => f y - ν.mean f) =
      ∑ y, centeredKernelMatrix ν K x y * f y := by
    rw [centeredKernelMatrix_apply, FiniteProbabilityWeights.mean_sub, FiniteProbabilityWeights.mean_const]
  simp_rw [he] at hc
  rw [ν.mean_centered_sq] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hC)

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConditioningShellError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_conditioningShellSupports (I A B : Finset ι) (b : ℕ) :
    B ∈ conditioningShellSupports I A b ↔ B ⊆ Iᶜ ∧ b - I.card < B.card ∧ A.card + B.card ≤ b := by
  simp only [conditioningShellSupports, Finset.mem_filter, Finset.mem_powerset]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProductDensityRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_empty (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ ∅ f x = (FiniteProbabilityWeights.pi μ).mean f := by
  simp [productANOVA, productConditionalMean_empty]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorePairingSplit
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_empty (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVA μ ∅ w) (productANOVA ν ∅ f) =
      (FiniteProbabilityWeights.pi μ).mean w * (FiniteProbabilityWeights.pi ν).mean f := by
  simp only [productCouplingPairing, productANOVA_empty, FiniteProbabilityWeights.mean_const]

theorem productCouplingPairing_core_split (J : Finset ι) {r b : ℕ} (hrb : r ≤ b)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ (restrictedDegreeSupports J b) w)
      (productANOVATruncation ν (restrictedDegreeSupports J b) f) =
      (FiniteProbabilityWeights.pi μ).mean w * (FiniteProbabilityWeights.pi ν).mean f +
        (∑ k ∈ Finset.range r, productCouplingPairing c
          (productANOVATruncation μ (J.powersetCard (k + 1)) w)
          (productANOVATruncation ν (J.powersetCard (k + 1)) f)) +
        productCouplingPairing c (productANOVATruncation μ (degreeTailSupports J r b) w)
          (productANOVATruncation ν (degreeTailSupports J r b) f) := by
  simp only [productCouplingPairing_truncation]
  rw [sum_restrictedDegreeSupports_split J hrb, sum_restrictedDegreeSupports_zero,
    productCouplingPairing_empty]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteLowLevelSeries
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem low_level_series_bound {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (r : ℕ) :
    (∑ j ∈ Finset.range r, u ^ (j + 1)) ≤ 2 * u := by
  have hs (n : ℕ) : (∑ j ∈ Finset.range n, u ^ j) ≤ 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [geom_sum_succ]
        nlinarith [mul_le_mul_of_nonneg_left ih hu0]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  nlinarith [mul_le_mul_of_nonneg_right (hs r) hu0]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialProductDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem product_piecewise_split (S : Finset ι) (a b : ι → ℝ) :
    (∏ i, if i ∈ S then a i else b i) = (∏ i ∈ S, a i) * ∏ i ∈ Finset.univ \ S, b i := by
  rw [Finset.prod_ite]
  have h₁ : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
  have h₂ : Finset.univ.filter (fun i => i ∉ S) = Finset.univ \ S := by ext i; simp
  rw [h₁, h₂]

theorem partial_product_difference (S : Finset ι) (a b : ι → ℝ) :
    (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * (∏ i, if i ∈ S \ U then a i else b i)) =
      ∏ i, if i ∈ S then a i - b i else b i := by
  calc
    _ = (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * (∏ i ∈ S \ U, a i) * ∏ i ∈ U, b i) *
        ∏ i ∈ Finset.univ \ S, b i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U hU
      have hUS := Finset.mem_powerset.mp hU
      have he : Finset.univ \ (S \ U) = (Finset.univ \ S) ∪ U := by
        ext i
        by_cases hi : i ∈ S <;> by_cases hu : i ∈ U <;> simp_all
      have hd : Disjoint (Finset.univ \ S) U := by
        apply Finset.disjoint_left.mpr
        intro i hi hu
        exact (Finset.mem_sdiff.mp hi).2 (hUS hu)
      rw [product_piecewise_split, he, Finset.prod_union hd]
      ring
    _ = (∏ i ∈ S, (a i - b i)) * ∏ i ∈ Finset.univ \ S, b i := by
      rw [← Finset.prod_sub]
    _ = _ := (product_piecewise_split S (fun i => a i - b i) b).symm

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductKernelPairing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*} [∀ i, Fintype (X i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (f : (∀ i, X i) → ℝ) :
    (pi p).mean f = (p 0).mean (fun a =>
      (pi (fun i : Fin n => p i.succ)).mean (fun y => f (Fin.cons a y))) := by
  have h := congrArg Complex.re (complexMean_pi_fin_cons p (fun x => (f x : ℂ)))
  simpa only [complexMean_re, Complex.ofReal_re] using h

theorem mean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (f : (∀ i, X i) → ℝ) :
    p.mean f = f (fun i => Fin.elim0 i) := by
  have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg f (Subsingleton.elim _ _)
  rw [hf, p.mean_const]

end FiniteProbabilityWeights

theorem productMatrixApply_empty {X Y : Fin 0 → Type*} [∀ i, Fintype (Y i)]
    (A : ∀ i, X i → Y i → ℝ) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productMatrixApply A f x = f (fun i => Fin.elim0 i) := by
  classical
  simp only [productMatrixApply, Fin.prod_univ_zero, one_mul, Fintype.sum_unique]
  congr 1

theorem productMatrixApply_fin_cons {n : ℕ} {X Y : Fin (n + 1) → Type*}
    [∀ i, Fintype (Y i)] (A : ∀ i, X i → Y i → ℝ) (f : (∀ i, Y i) → ℝ)
    (x : X 0) (u : ∀ i : Fin n, X i.succ) :
    productMatrixApply A f (Fin.cons x u) = ∑ y : Y 0, A 0 x y *
      productMatrixApply (fun i : Fin n => A i.succ) (fun v => f (Fin.cons y v)) u := by
  simp only [productMatrixApply, sum_dependent_fin_cons, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]

theorem productMatrixApply_sq_le_fin {n : ℕ} {X Y : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (A : ∀ i, X i → Y i → ℝ) (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hA : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (∑ y, A i x y * f y) ^ 2) ≤
      C i * (ν i).mean (fun y => f y ^ 2)) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productMatrixApply A f x ^ 2) ≤
      (∏ i, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  induction n with
  | zero =>
      simp only [productMatrixApply_empty, Fin.prod_univ_zero, one_mul,
        FiniteProbabilityWeights.mean_const, FiniteProbabilityWeights.mean_empty_tuple]
      exact le_rfl
  | succ n ih =>
      rw [FiniteProbabilityWeights.mean_pi_fin_cons]
      simp_rw [productMatrixApply_fin_cons]
      rw [FiniteProbabilityWeights.mean_comm]
      calc
        _ ≤ (FiniteProbabilityWeights.pi (fun i : Fin n => μ i.succ)).mean
            (fun x => C 0 * (ν 0).mean (fun y =>
              productMatrixApply (fun i : Fin n => A i.succ) (fun v => f (Fin.cons y v)) x ^ 2)) :=
          FiniteProbabilityWeights.mean_mono _ (fun x => hA 0 _)
        _ = C 0 * (ν 0).mean (fun y =>
            (FiniteProbabilityWeights.pi (fun i : Fin n => μ i.succ)).mean
              (fun x => productMatrixApply (fun i : Fin n => A i.succ) (fun v => f (Fin.cons y v)) x ^ 2)) := by
          rw [FiniteProbabilityWeights.mean_const_mul, FiniteProbabilityWeights.mean_comm]
        _ ≤ C 0 * (ν 0).mean (fun y => (∏ i : Fin n, C i.succ) *
            (FiniteProbabilityWeights.pi (fun i : Fin n => ν i.succ)).mean
              (fun v => f (Fin.cons y v) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (hC 0)
          apply FiniteProbabilityWeights.mean_mono
          intro y
          exact ih (fun i => μ i.succ) (fun i => ν i.succ) (fun i => A i.succ)
            (fun i => C i.succ) (fun i => hC i.succ) (fun i => hA i.succ) (fun v => f (Fin.cons y v))
        _ = _ := by
          rw [FiniteProbabilityWeights.mean_const_mul, Fin.prod_univ_succ,
            FiniteProbabilityWeights.mean_pi_fin_cons]
          ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

omit [∀ i, Fintype (X i)] in
theorem productMatrixApply_reindex (A : ∀ i, X i → Y i → ℝ) (e : κ ≃ ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productMatrixApply A f x = productMatrixApply (fun j => A (e j))
      (fun y => f (Equiv.piCongrLeft Y e y)) (fun j => x (e j)) := by
  classical
  unfold productMatrixApply
  apply Fintype.sum_equiv (Equiv.piCongrLeft Y e).symm
  intro y
  simp only [Equiv.apply_symm_apply, Equiv.piCongrLeft_symm_apply]
  rw [e.prod_comp (fun i => A i (x i) (y i))]

omit [Fintype κ] [DecidableEq κ] in
theorem productMatrixApply_sq_le (μ : ∀ i, FiniteProbabilityWeights (X i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (A : ∀ i, X i → Y i → ℝ)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hA : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (∑ y, A i x y * f y) ^ 2) ≤
      C i * (ν i).mean (fun y => f y ^ 2)) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productMatrixApply A f x ^ 2) ≤
      (∏ i, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  let e := (Fintype.equivFin ι).symm
  let eY := Equiv.piCongrLeft Y e
  have hh := productMatrixApply_sq_le_fin (fun j => μ (e j)) (fun j => ν (e j))
    (fun j => A (e j)) (fun j => C (e j)) (fun j => hC (e j)) (fun j => hA (e j))
    (fun y => f (eY y))
  have hleft := productMean_reindex μ e
    (fun x => productMatrixApply (fun j => A (e j)) (fun y => f (eY y)) x ^ 2)
  rw [← hleft] at hh
  have heval (x : ∀ i, X i) : productMatrixApply (fun j => A (e j))
      (fun y => f (eY y)) (fun j => x (e j)) = productMatrixApply A f x :=
    (productMatrixApply_reindex A e f x).symm
  simp_rw [heval] at hh
  have hright := productMean_reindex ν e (fun y => f (eY y) ^ 2)
  have he (y : ∀ i, Y i) : eY (fun j => y (e j)) = y := eY.apply_symm_apply y
  simp_rw [he] at hright
  rw [← hright, e.prod_comp C] at hh
  exact hh

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

theorem productCouplingPairing_ofKernel (μ : ∀ i, FiniteProbabilityWeights (X i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)) w f =
      (FiniteProbabilityWeights.pi μ).mean
        (fun x => w x * productMatrixApply (fun i x y => (K i x).weight y) f x) := by
  change (FiniteProbabilityWeights.pi (fun i => (μ i).joint (K i))).mean
    (fun z => w (fun i => (z i).1) * f (fun i => (z i).2)) = _
  rw [productJoint_mean μ K (fun x y => w x * f y)]
  simp only [FiniteProbabilityWeights.mean_const_mul]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProductMixedLaws
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]

theorem productMean_mix_laws (p q : ∀ i, FiniteProbabilityWeights (Y i))
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi p).mean (fun x => (FiniteProbabilityWeights.pi q).mean
      (fun y => f (productCoordinateMix S x y))) =
      (FiniteProbabilityWeights.pi (fun i => if i ∈ S then p i else q i)).mean f := by
  rw [← productJoint_mean p (fun i _ => q i) (fun x y => f (productCoordinateMix S x y))]
  have h : ∀ i (g : Y i → ℝ), ((p i).joint (fun _ => q i)).mean
      (fun z => g (if i ∈ S then z.1 else z.2)) =
        (if i ∈ S then p i else q i).mean g := by
    intro i g
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, FiniteProbabilityWeights.joint_mean, FiniteProbabilityWeights.mean_const]
    · simp only [hi, ite_false, FiniteProbabilityWeights.joint_mean, FiniteProbabilityWeights.mean_const]
  unfold productCoordinateMix
  exact productMean_coordinate_transport (fun i => (p i).joint (fun _ => q i))
      (fun i => if i ∈ S then p i else q i)
      (fun i (z : Y i × Y i) => if i ∈ S then z.1 else z.2) h f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelSupportContraction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

theorem productKernelApply_conditional (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (productConditionalMean ν S f) x =
      (FiniteProbabilityWeights.pi (fun i => if i ∈ S then K i (x i) else ν i)).mean f :=
  productMean_mix_laws (fun i => K i (x i)) ν S f

theorem productKernelApply_sum {J : Type*} (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (D : Finset J) (f : J → (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (fun y => ∑ j ∈ D, f j y) x = ∑ j ∈ D, productKernelApply K (f j) x :=
  FiniteProbabilityWeights.mean_sum _ D f

theorem productKernelApply_smul (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (c : ℝ) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (fun y => c * f y) x = c * productKernelApply K f x :=
  FiniteProbabilityWeights.mean_const_mul _ c f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

theorem productKernelApply_ANOVA (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (productANOVA ν S f) x = productMatrixApply (anovaKernelMatrix ν K S) f x := by
  have hT (T : Finset ι) : productKernelApply K (productConditionalMean ν T f) x =
      ∑ y, (∏ i, if i ∈ T then (K i (x i)).weight (y i) else (ν i).weight (y i)) * f y := by
    rw [productKernelApply_conditional]
    simp only [FiniteProbabilityWeights.mean, FiniteProbabilityWeights.pi]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ T <;> simp only [hi, ite_true, ite_false]
  change productKernelApply K (fun y => ∑ U ∈ S.powerset,
    (-1 : ℝ) ^ U.card * productConditionalMean ν (S \ U) f y) x = _
  rw [productKernelApply_sum]
  simp_rw [productKernelApply_smul, hT, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold productMatrixApply
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
        (∏ i, if i ∈ S \ U then (K i (x i)).weight (y i) else (ν i).weight (y i))) * f y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U _
      ring
    _ = _ := by
      rw [partial_product_difference]
      rfl

theorem productKernelApply_ANOVA_active (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productMatrixApply (anovaKernelMatrix ν K S) (productANOVA ν S f) x =
      productKernelApply K (productANOVA ν S f) x := by
  rw [← productKernelApply_ANOVA]
  have he : productANOVA ν S (productANOVA ν S f) = productANOVA ν S f :=
    funext (productANOVA_idempotent ν S f)
  rw [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
  (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
  (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
    (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))

include hC hbound

theorem anovaKernelMatrix_sq_le (S : Finset ι) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productMatrixApply (anovaKernelMatrix ν K S) f x ^ 2) ≤
      (∏ i ∈ S, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  have hc (i : ι) : 0 ≤ if i ∈ S then C i else 1 := by
    split_ifs
    · exact hC i
    · exact zero_le_one
  have ha (i : ι) (g : Y i → ℝ) :
      (μ i).mean (fun x => (∑ y, anovaKernelMatrix ν K S i x y * g y) ^ 2) ≤
        (if i ∈ S then C i else 1) * (ν i).mean (fun y => g y ^ 2) := by
    by_cases hi : i ∈ S
    · simp only [anovaKernelMatrix, hi, ite_true]
      exact centeredKernelMatrix_sq_le (μ i) (ν i) (K i) (hC i) (hbound i) g
    · simp only [anovaKernelMatrix, hi, ite_false, one_mul]
      change (μ i).mean (fun _ => (ν i).mean g ^ 2) ≤ _
      rw [FiniteProbabilityWeights.mean_const]
      exact (ν i).mean_square_le g
  simpa only [Fintype.prod_ite_mem] using
    productMatrixApply_sq_le μ ν (anovaKernelMatrix ν K S) (fun i => if i ∈ S then C i else 1) hc ha f

theorem productKernelApply_ANOVA_sq_le (S : Finset ι) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productKernelApply K (productANOVA ν S f) x ^ 2) ≤
      (∏ i ∈ S, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => productANOVA ν S f y ^ 2) := by
  simpa only [productKernelApply_ANOVA_active] using
    anovaKernelMatrix_sq_le μ ν K C hC hbound S (productANOVA ν S f)

theorem productCouplingPairing_support_sq_le
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (S : Finset ι) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVA μ S w) (productANOVA ν S f) ^ 2 ≤
        (∏ i ∈ S, C i) * (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S w x ^ 2) *
          (FiniteProbabilityWeights.pi ν).mean (fun y => productANOVA ν S f y ^ 2) := by
  rw [productCouplingPairing_ofKernel]
  change ((FiniteProbabilityWeights.pi μ).mean
    (fun x => productANOVA μ S w x * productKernelApply K (productANOVA ν S f) x)) ^ 2 ≤ _
  have hcs := (FiniteProbabilityWeights.pi μ).mean_mul_sq_le (productANOVA μ S w)
    (productKernelApply K (productANOVA ν S f))
  have hn := productKernelApply_ANOVA_sq_le μ ν K C hC hbound S f
  have hm := mul_le_mul_of_nonneg_left hn
    ((FiniteProbabilityWeights.pi μ).mean_nonneg (fun x => sq_nonneg (productANOVA μ S w x)))
  exact (hcs.trans hm).trans_eq (by ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportPairingAggregation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productCouplingPairing_truncation_abs_le
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (D : Finset (Finset ι)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hprod : ∀ S ∈ D, (∏ i ∈ S, C i) ≤ ρ ^ 2)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
        ρ * Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have ha (S : Finset ι) : 0 ≤ (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S w x ^ 2) :=
    FiniteProbabilityWeights.mean_nonneg _ (fun x => sq_nonneg (productANOVA μ S w x))
  have hb (S : Finset ι) : 0 ≤ (FiniteProbabilityWeights.pi ν).mean (fun x => productANOVA ν S f x ^ 2) :=
    FiniteProbabilityWeights.mean_nonneg _ (fun x => sq_nonneg (productANOVA ν S f x))
  have hpoint (S : Finset ι) (hS : S ∈ D) :
      productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f) ^ 2 ≤
        (ρ ^ 2 * (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S w x ^ 2)) *
          (FiniteProbabilityWeights.pi ν).mean (fun x => productANOVA ν S f x ^ 2) :=
    (productCouplingPairing_support_sq_le μ ν K C hC hbound hK S w f).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hprod S hS) (ha S)) (hb S))
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul D
    (fun S _ => mul_nonneg (sq_nonneg ρ) (ha S)) (fun S _ => hb S) hpoint
  rw [← Finset.mul_sum] at hs
  change (∑ S ∈ D, productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f)) ^ 2 ≤
    ρ ^ 2 * productANOVAEnergy μ D w * productANOVAEnergy ν D f at hs
  rw [productCouplingPairing_truncation]
  calc
    _ = Real.sqrt ((∑ S ∈ D, productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f)) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (ρ ^ 2 * productANOVAEnergy μ D w * productANOVAEnergy ν D f) := Real.sqrt_le_sqrt hs
    _ = _ := by
      rw [Real.sqrt_mul (mul_nonneg (sq_nonneg ρ) (productANOVAEnergy_nonneg μ D w)),
        Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoreComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem productCouplingPairing_restricted_tail_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (J : Finset ι) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i ∈ J, C i ≤ κ ^ 2) (r : ℕ) (D : Finset (Finset ι))
    (hsub : ∀ S ∈ D, S ⊆ J) (hmin : ∀ S ∈ D, r ≤ S.card)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
      κ ^ r * Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  apply productCouplingPairing_truncation_abs_le μ ν K C hC hbound hK D (pow_nonneg hκ0 r) _ w f
  intro S hS
  have hp : (∏ i ∈ S, C i) ≤ (κ ^ S.card) ^ 2 := by
    calc
      _ ≤ ∏ _i ∈ S, κ ^ 2 := Finset.prod_le_prod (fun i _ => hC i) (fun i hi => hcap i (hsub S hS hi))
      _ = _ := by rw [Finset.prod_const, ← pow_mul, ← pow_mul, Nat.mul_comm 2 S.card]
  exact hp.trans (pow_le_pow_left₀ (pow_nonneg hκ0 S.card)
    (pow_le_pow_of_le_one hκ0 hκ1 (hmin S hS)) 2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_conditioning_shell_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    {κ M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ A ∈ I.powerset,
      Real.sqrt (productANOVAEnergy μ (conditioningShellSupports I A b) (productSectionAverage μ I I x w)) ≤ M)
    (hf : ∀ A ∈ I.powerset,
      Real.sqrt (productANOVAEnergy ν (conditioningShellSupports I A b) (productSectionAverage ν I I y f)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) := by
  dsimp only
  apply productCouplingPairing_conditioning_error_le_s2 _ I b hIb x y w f
  intro A hA
  have hs (S : Finset ι) (hS : S ∈ conditioningShellSupports I A b) :=
    (mem_conditioningShellSupports I A S b).mp hS
  have ht := productCouplingPairing_restricted_tail_abs_le μ ν K C hC hbound hK Iᶜ hκ0 hκ1
    (fun i hi => hcap i (Finset.mem_compl.mp hi)) (b - I.card) (conditioningShellSupports I A b)
    (fun S hS => (hs S hS).1) (fun S hS => (hs S hS).2.1.le)
    (productSectionAverage μ I I x w) (productSectionAverage ν I I y f)
  apply ht.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hw A hA) (pow_nonneg hκ0 _)) (hf A hA)
    (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg hκ0 _) ((Real.sqrt_nonneg _).trans (hw A hA)))

theorem productKernel_conditioning_shell_of_truncated {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    {κ M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b) (productSectionAverage μ I I x w)) ≤ M)
    (hf : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) (productSectionAverage ν I I y f)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) := by
  have hsub (A : Finset ι) : conditioningShellSupports I A b ⊆ lowDegreeCoordinateSets ι b := by
    intro S hS
    have hh := (mem_conditioningShellSupports I A S b).mp hS
    apply (mem_lowDegreeCoordinateSets ι b S).mpr
    omega
  apply productKernel_conditioning_shell_bound μ ν K C hC hbound hK I b hIb hκ0 hκ1 hcap x y w f
  · intro A _
    exact (Real.sqrt_le_sqrt (productANOVAEnergy_mono μ (hsub A) _)).trans hw
  · intro A _
    exact (Real.sqrt_le_sqrt (productANOVAEnergy_mono ν (hsub A) _)).trans hf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
  (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
  (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
    (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
  (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)

include hC hbound

theorem productCouplingPairing_restricted_level_of_bounds (J : Finset ι)
    {κ A B : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∈ J, C i ≤ κ ^ 2)
    (k : ℕ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A)
    (hf : Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ (J.powersetCard k) w)
      (productANOVATruncation ν (J.powersetCard k) f)| ≤ κ ^ k * A * B := by
  have hcard (S : Finset ι) (hS : S ∈ J.powersetCard k) := (Finset.mem_powersetCard.mp hS).2
  have hwr := (Real.sqrt_le_sqrt (productANOVAEnergy_le_level μ (J.powersetCard k) k hcard w)).trans hw
  have hfr := (Real.sqrt_le_sqrt (productANOVAEnergy_le_level ν (J.powersetCard k) k hcard f)).trans hf
  have ht := productCouplingPairing_restricted_tail_abs_le μ ν K C hC hbound hK J hκ0 hκ1 hcap k
    (J.powersetCard k) (fun S hS => (Finset.mem_powersetCard.mp hS).1)
    (fun S hS => (hcard S hS).ge) w f
  apply ht.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hwr (pow_nonneg hκ0 k)) hfr (Real.sqrt_nonneg _)
    (mul_nonneg (pow_nonneg hκ0 k) ((Real.sqrt_nonneg _).trans hwr))

theorem productCouplingPairing_restricted_low_levels_small (J : Finset ι)
    {κ A B : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∈ J, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2) (r : ℕ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B ^ (2 * k)) :
    |∑ j ∈ Finset.range r, productCouplingPairing
      (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ (J.powersetCard (j + 1)) w)
      (productANOVATruncation ν (J.powersetCard (j + 1)) f)| ≤ 2 * (κ * A ^ 2 * B ^ 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range r, |productCouplingPairing
        (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
        (productANOVATruncation μ (J.powersetCard (j + 1)) w)
        (productANOVATruncation ν (J.powersetCard (j + 1)) f)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range r, (κ * A ^ 2 * B ^ 2) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hle : j + 1 ≤ r := Finset.mem_range.mp hj
      have hb := productCouplingPairing_restricted_level_of_bounds μ ν K C hC hbound hK J hκ0 hκ1 hcap
        (j + 1) w f (hw (j + 1) (by omega) hle) (hf (j + 1) (by omega) hle)
      exact hb.trans_eq (by rw [mul_pow, mul_pow, pow_mul, pow_mul])
    _ ≤ _ := low_level_series_bound (by positivity) hsmall r

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_core_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (J : Finset ι) {r b : ℕ} (hrb : r ≤ b)
    {κ A B M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∈ J, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b) w) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) f) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c (productANOVATruncation μ (restrictedDegreeSupports J b) w)
      (productANOVATruncation ν (restrictedDegreeSupports J b) f) -
      (FiniteProbabilityWeights.pi μ).mean w * (FiniteProbabilityWeights.pi ν).mean f| ≤
      2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have hlo := productCouplingPairing_restricted_low_levels_small μ ν K C hC hbound hK J
    hκ0 hκ1 hcap hsmall r w f hw hf
  have hsub : degreeTailSupports J r b ⊆ lowDegreeCoordinateSets ι b := by
    intro S hS
    exact (mem_lowDegreeCoordinateSets ι b S).mpr ((mem_degreeTailSupports J S r b).mp hS).2.2
  have hwm := (Real.sqrt_le_sqrt (productANOVAEnergy_mono μ hsub w)).trans hM
  have hfn := (Real.sqrt_le_sqrt (productANOVAEnergy_mono ν hsub f)).trans hN
  have ht := productCouplingPairing_restricted_tail_abs_le μ ν K C hC hbound hK J hκ0 hκ1 hcap r
    (degreeTailSupports J r b) (fun S hS => ((mem_degreeTailSupports J S r b).mp hS).1)
    (fun S hS => ((mem_degreeTailSupports J S r b).mp hS).2.1.le) w f
  have htail : |productCouplingPairing c (productANOVATruncation μ (degreeTailSupports J r b) w)
      (productANOVATruncation ν (degreeTailSupports J r b) f)| ≤ κ ^ r * M * N :=
    ht.trans (mul_le_mul (mul_le_mul_of_nonneg_left hwm (pow_nonneg hκ0 r)) hfn
      (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg hκ0 r) ((Real.sqrt_nonneg _).trans hwm)))
  calc
    _ = |(∑ k ∈ Finset.range r, productCouplingPairing c
          (productANOVATruncation μ (J.powersetCard (k + 1)) w)
          (productANOVATruncation ν (J.powersetCard (k + 1)) f)) +
        productCouplingPairing c (productANOVATruncation μ (degreeTailSupports J r b) w)
          (productANOVATruncation ν (degreeTailSupports J r b) f)| := by
      rw [productCouplingPairing_core_split c J hrb]
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hlo htail)

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

theorem normalized_pairing_error_scale {P u v q m s E : ℝ} (hm : 0 < m) (hs : 0 < s)
    (h : |m⁻¹ * s⁻¹ * P - q * ((m⁻¹ * u) * (s⁻¹ * v))| ≤ E) :
    |P - q * (u * v)| ≤ m * s * E := by
  calc
    _ = |(m * s) * (m⁻¹ * s⁻¹ * P - q * ((m⁻¹ * u) * (s⁻¹ * v)))| := by
      congr 1
      field_simp
    _ = m * s * |m⁻¹ * s⁻¹ * P - q * ((m⁻¹ * u) * (s⁻¹ * v))| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hm.le hs.le)]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (mul_nonneg hm.le hs.le)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productAtomTruncatedPairing_smul (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) (a b : ℝ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productAtomTruncatedPairing c D I x y (fun z => a * w z) (fun z => b * f z) =
      a * b * productAtomTruncatedPairing c D I x y w f := by
  have hw : (fun z => productFiberIndicator I x z * (a * w z)) =
      (fun z => a * (productFiberIndicator I x z * w z)) := by funext z; ring
  have hf : (fun z => productFiberIndicator I y z * (b * f z)) =
      (fun z => b * (productFiberIndicator I y z * f z)) := by funext z; ring
  unfold productAtomTruncatedPairing
  rw [hw, hf, productCouplingPairing_truncation_smul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem weighted_pairing_error_compose {P Q R m E F : ℝ} (hm : 0 ≤ m)
    (hP : |P - m * Q| ≤ E) (hQ : |Q - R| ≤ F) : |P - m * R| ≤ E + m * F := by
  calc
    _ = |(P - m * Q) + m * (Q - R)| := by congr 1; ring
    _ ≤ |P - m * Q| + |m * (Q - R)| := abs_add_le _ _
    _ = |P - m * Q| + m * |Q - R| := by rw [abs_mul, abs_of_nonneg hm]
    _ ≤ _ := add_le_add hP (mul_le_mul_of_nonneg_left hQ hm)

theorem productKernel_conditioned_mean_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) {r b : ℕ} (hIb : I.card ≤ b) (hr : r ≤ b - I.card)
    {κ A B M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (productSectionAverage μ I I x w)) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (productSectionAverage ν I I y f)) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b) (productSectionAverage μ I I x w)) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) (productSectionAverage ν I I y f)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y *
        ((FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ I I x w) *
         (FiniteProbabilityWeights.pi ν).mean (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) +
        productCouplingAtomMass c I x y * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N) := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have hsub : lowDegreeCoordinateSets ι (b - I.card) ⊆ lowDegreeCoordinateSets ι b := by
    intro S hS
    exact (mem_lowDegreeCoordinateSets ι b S).mpr
      (((mem_lowDegreeCoordinateSets ι (b - I.card) S).mp hS).trans (Nat.sub_le b I.card))
  have hcore := productKernel_core_comparison μ ν K C hC hbound hK Iᶜ hr hκ0 hκ1
    (fun i hi => hcap i (Finset.mem_compl.mp hi)) hsmall
    (productSectionAverage μ I I x w) (productSectionAverage ν I I y f) hw hf
    ((Real.sqrt_le_sqrt (productANOVAEnergy_mono μ hsub _)).trans hM)
    ((Real.sqrt_le_sqrt (productANOVAEnergy_mono ν hsub _)).trans hN)
  have hshell := productKernel_conditioning_shell_of_truncated μ ν K C hC hbound hK I b hIb
    hκ0 hκ1 hcap x y w f hM hN
  exact weighted_pairing_error_compose (productCouplingAtomMass_nonneg c I x y) hshell hcore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_scaled_conditioned_mean_comparison_s2_oai {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) {r b : ℕ} (hIb : I.card ≤ b) (hr : r ≤ b - I.card)
    {κ A B M N m s : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (fun z => s⁻¹ * productSectionAverage ν I I y f z)) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
      (fun z => s⁻¹ * productSectionAverage ν I I y f z)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w f -
      productCouplingAtomMass c I x y *
        (productConditionalMean μ I w x * productConditionalMean ν I f y)| ≤
      m * s * ((2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) +
        productCouplingAtomMass c I x y * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N)) := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have hw_eq : productSectionAverage μ I I x (fun z => m⁻¹ * w z) =
      (fun z => m⁻¹ * productSectionAverage μ I I x w z) :=
    funext (productSectionAverage_smul μ I I x m⁻¹ w)
  have hf_eq : productSectionAverage ν I I y (fun z => s⁻¹ * f z) =
      (fun z => s⁻¹ * productSectionAverage ν I I y f z) :=
    funext (productSectionAverage_smul ν I I y s⁻¹ f)
  have h := productKernel_conditioned_mean_comparison μ ν K C hC hbound hK I hIb hr
    hκ0 hκ1 hcap hsmall x y (fun z => m⁻¹ * w z) (fun z => s⁻¹ * f z)
    (by simpa only [hw_eq] using hw) (by simpa only [hf_eq] using hf)
    (by simpa only [hw_eq] using hM) (by simpa only [hf_eq] using hN)
  change |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y
      (fun z => m⁻¹ * w z) (fun z => s⁻¹ * f z) - productCouplingAtomMass c I x y *
      ((FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ I I x (fun z => m⁻¹ * w z)) *
       (FiniteProbabilityWeights.pi ν).mean (productSectionAverage ν I I y (fun z => s⁻¹ * f z)))| ≤ _ at h
  rw [productAtomTruncatedPairing_smul, productSectionAverage_self_mean, productSectionAverage_self_mean,
    productConditionalMean_smul, productConditionalMean_smul] at h
  exact normalized_pairing_error_scale hm hs h

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.productKernel_scaled_conditioned_mean_comparison_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.productKernel_scaled_conditioned_mean_comparison_s2_oai.{u_1, u_2, u_3}
