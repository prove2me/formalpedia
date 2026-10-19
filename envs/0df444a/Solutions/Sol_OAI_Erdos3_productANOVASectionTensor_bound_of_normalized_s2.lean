-- Prove2me | solution 1 for OAI.Erdos3.productANOVASectionTensor_bound_of_normalized_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:25:46.169466+00:00
-- url     : https://prove2.me/submissions/4c8b3b16-bbc3-4012-a5d5-2036f908e5fc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B139

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteOrderedSubsetSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

theorem finiteOrderedSubset_sum (k : ℕ) (g : Finset I → ℝ) :
    (∑ a : Fin k → I, if StrictMono a then g (Finset.univ.image a) else 0) =
      ∑ S ∈ Finset.univ.powersetCard k, g S := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun a _ => Finset.univ.image a)
    (fun S hS => S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have hm : StrictMono a := (Finset.mem_filter.mp ha).2
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_image_of_injective Finset.univ hm.injective⟩
  · intro S hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (S.orderEmbOfFin _).strictMono⟩
  · intro a ha
    have hm : StrictMono a := (Finset.mem_filter.mp ha).2
    exact (Finset.orderEmbOfFin_unique _ (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩) hm).symm
  · intro S hS
    exact Finset.image_orderEmbOfFin_univ S _
  · intro a _
    rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionPermutation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_two (w : X → ℝ) (f : X → ℝ) :
    finiteWeightedLp w 2 f = Real.sqrt (∑ x, w x * f x ^ 2) := by
  simp only [finiteWeightedLp, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem norm_finiteWeightedL2Map (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (f : X → ℝ) :
    ‖finiteWeightedL2Map w f‖ = finiteWeightedLp w 2 f := by
  rw [EuclideanSpace.norm_eq, finiteWeightedLp_two]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change |Real.sqrt (w x) * f x| ^ 2 = w x * f x ^ 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (hw x)]

theorem finiteWeightedLp_two_sum_le {J : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (D : Finset J) (f : J → X → ℝ) :
    finiteWeightedLp w 2 (fun x => ∑ j ∈ D, f j x) ≤ ∑ j ∈ D, finiteWeightedLp w 2 (f j) := by
  have he : (fun x => ∑ j ∈ D, f j x) = ∑ j ∈ D, f j := by
    funext x
    simp only [Finset.sum_apply]
  rw [he, ← norm_finiteWeightedL2Map w hw, map_sum]
  exact (norm_sum_le D (fun j => finiteWeightedL2Map w (f j))).trans_eq
    (Finset.sum_congr rfl (fun j _ => norm_finiteWeightedL2Map w hw (f j)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω J L : Type*} [Fintype Ω]

theorem FiniteProbabilityWeights.familyL2_eq (p : FiniteProbabilityWeights Ω)
    (E : Finset L) (g : L → Ω → ℝ) :
    finiteWeightedLp (fun v : ↥E × Ω => p.weight v.2) 2 (fun v => g v.1 v.2) =
      Real.sqrt (∑ l ∈ E, p.mean (fun x => g l x ^ 2)) := by
  rw [finiteWeightedLp_two, Fintype.sum_prod_type]
  congr 1
  exact Finset.sum_coe_sort E (fun l => p.mean (fun x => g l x ^ 2))

theorem FiniteProbabilityWeights.sqrt_sum_mean_sq_triangle (p : FiniteProbabilityWeights Ω)
    (D : Finset J) (E : Finset L) (f : J → L → Ω → ℝ) :
    Real.sqrt (∑ l ∈ E, p.mean (fun x => (∑ j ∈ D, f j l x) ^ 2)) ≤
      ∑ j ∈ D, Real.sqrt (∑ l ∈ E, p.mean (fun x => f j l x ^ 2)) := by
  have h := finiteWeightedLp_two_sum_le (fun v : ↥E × Ω => p.weight v.2)
    (fun v => p.nonneg v.2) D (fun j v => f j v.1 v.2)
  rw [p.familyL2_eq E (fun l x => ∑ j ∈ D, f j l x)] at h
  simpa only [p.familyL2_eq] using h

end Erdos3

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

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_eq_normalized (T A : Finset I) (z : ∀ i, X i)
    {K : ℝ} (hK : K ≠ 0) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z f x = K ^ A.card * productNormalizedSection μ T A z K f x := by
  simp only [productNormalizedSection, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hK), one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductDependsOnMix
namespace OAI

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem ProductDependsOn.mix {S T : Finset I} {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn (S ∪ T) f) (z : ∀ i, X i) :
    ProductDependsOn T (fun x => f (productCoordinateMix S z x)) := by
  intro x y hxy
  apply hf
  intro i hi
  by_cases hs : i ∈ S
  · simp only [productCoordinateMix, hs, ite_true]
  · have ht : i ∈ T := (Finset.mem_union.mp hi).resolve_left hs
    simp only [productCoordinateMix, hs, ite_false, hxy i ht]

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_sectionAverage (T A U : Finset I) (hAT : A ⊆ T)
    (hTU : Disjoint T U) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ U (productSectionAverage μ T A z f) x =
      ∑ B ∈ U.powerset, (-1 : ℝ) ^ (U.card - B.card) *
        productConditionalMean μ (A ∪ B) f (productCoordinateMix T z x) := by
  rw [productANOVA_inclusion_exclusion]
  apply Finset.sum_congr rfl
  intro B hB
  rw [productConditionalMean_sectionAverage μ T A B hAT]
  have hBT : Disjoint B T := hTU.symm.mono_left (Finset.mem_powerset.mp hB)
  rw [Finset.sdiff_eq_self_of_disjoint hBT]

theorem productANOVA_disjoint_section (T U : Finset I) (hTU : Disjoint T U)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ (T ∪ U) f (productCoordinateMix T z x) =
      ∑ A ∈ T.powerset, (-1 : ℝ) ^ (T.card - A.card) *
        productANOVA μ U (productSectionAverage μ T A z f) x := by
  rw [productANOVA_inclusion_exclusion, disjoint_powerset_sum T U hTU]
  apply Finset.sum_congr rfl
  intro A hA
  have hAT := Finset.mem_powerset.mp hA
  rw [productANOVA_sectionAverage μ T A U hAT hTU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hBU := Finset.mem_powerset.mp hB
  have hAB : Disjoint A B := hTU.mono hAT hBU
  have he : (T ∪ U).card - (A ∪ B).card = (T.card - A.card) + (U.card - B.card) := by
    rw [Finset.card_union_of_disjoint hTU, Finset.card_union_of_disjoint hAB]
    have ha := Finset.card_le_card hAT
    have hb := Finset.card_le_card hBU
    omega
  rw [he, pow_add, mul_assoc]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorGroupedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {J I : Type*} {X : I → Type*}

theorem finiteTaggedTuple_sum [Fintype I] [Fintype J] [DecidableEq J]
    [∀ i, Fintype (X i)] (F : (J → Sigma X) → ℝ) :
    (∑ z, F z) = ∑ a : J → I, ∑ v : ∀ j, X (a j), F (fun j => ⟨a j, v j⟩) := by
  classical
  calc
    (∑ z, F z) = ∑ av : Σ a : J → I, ∀ j, X (a j), F (fun j => ⟨av.1 j, av.2 j⟩) :=
      Fintype.sum_equiv finiteTaggedTupleEquiv _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem orderedFamilyTensor_energy (μ : ∀ i, FiniteProbabilityWeights (X i))
    (k : ℕ) (base : ∀ i, X i) (F : Finset I → (∀ i, X i) → ℝ)
    (hF : ∀ S, ProductDependsOn S (F S)) :
    finiteProductIntegral (fun _ : Fin k => coordinateUnionWeight μ)
      (fun z => orderedFamilyTensor k base F z ^ 2) =
        ∑ S ∈ Finset.univ.powersetCard k, (FiniteProbabilityWeights.pi μ).mean (fun x => F S x ^ 2) := by
  classical
  unfold finiteProductIntegral
  rw [finiteTaggedTuple_sum]
  calc
    _ = ∑ a : Fin k → I, if StrictMono a then
        (FiniteProbabilityWeights.pi μ).mean (fun x => F (Finset.univ.image a) x ^ 2) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : StrictMono a
      · simp only [orderedFamilyTensor, ha, dite_true, ite_true]
        refine productMean_tuple μ a ha.injective
          (fun x => F (Finset.univ.image a) x ^ 2) ?_ base
        intro x y hxy
        exact congrArg (fun t : ℝ => t ^ 2) (hF (Finset.univ.image a) x y hxy)
      · simp only [orderedFamilyTensor, ha, dite_false, ite_false,
          zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
    _ = _ := finiteOrderedSubset_sum k (fun S => (FiniteProbabilityWeights.pi μ).mean (fun x => F S x ^ 2))

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

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem sqrt_productANOVASectionEnergy_le (T : Finset I) (D : Finset (Finset I))
    (hD : ∀ U ∈ D, Disjoint T U) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤
      ∑ A ∈ T.powerset, Real.sqrt (productANOVAEnergy μ D (productSectionAverage μ T A z f)) := by
  have hsign (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have h := (FiniteProbabilityWeights.pi μ).sqrt_sum_mean_sq_triangle T.powerset D
    (fun A U x => (-1 : ℝ) ^ (T.card - A.card) *
      productANOVA μ U (productSectionAverage μ T A z f) x)
  have he : productANOVASectionEnergy μ T D z f =
      ∑ U ∈ D, (FiniteProbabilityWeights.pi μ).mean (fun x =>
        (∑ A ∈ T.powerset, (-1 : ℝ) ^ (T.card - A.card) *
          productANOVA μ U (productSectionAverage μ T A z f) x) ^ 2) := by
    apply Finset.sum_congr rfl
    intro U hU
    congr 1
    funext x
    rw [productANOVA_disjoint_section μ T U (hD U hU)]
  rw [he]
  simpa only [mul_pow, hsign, one_mul, productANOVAEnergy] using h

theorem sqrt_productANOVASectionEnergy_le_normalized (T : Finset I) (D : Finset (Finset I))
    (hD : ∀ U ∈ D, Disjoint T U) (z : ∀ i, X i) {K : ℝ} (hK : 0 < K)
    (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤
      ∑ A ∈ T.powerset, K ^ A.card *
        Real.sqrt (productANOVAEnergy μ D (productNormalizedSection μ T A z K f)) := by
  apply (sqrt_productANOVASectionEnergy_le μ T D hD z f).trans_eq
  apply Finset.sum_congr rfl
  intro A _
  have he : productSectionAverage μ T A z f =
      fun x => K ^ A.card * productNormalizedSection μ T A z K f x :=
    funext (productSectionAverage_eq_normalized μ T A z hK.ne' f)
  rw [he, sqrt_productANOVAEnergy_smul, abs_of_nonneg (pow_nonneg hK.le _)]

theorem sqrt_productANOVASectionEnergy_le_of_normalized (T : Finset I) (D : Finset (Finset I))
    (hD : ∀ U ∈ D, Disjoint T U) (z : ∀ i, X i) {K B : ℝ} (hK : 0 < K)
    (f : (∀ i, X i) → ℝ)
    (hB : ∀ A ∈ T.powerset,
      Real.sqrt (productANOVAEnergy μ D (productNormalizedSection μ T A z K f)) ≤ B) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤ (1 + K) ^ T.card * B := by
  apply (sqrt_productANOVASectionEnergy_le_normalized μ T D hD z hK f).trans
  calc
    (∑ A ∈ T.powerset, K ^ A.card *
      Real.sqrt (productANOVAEnergy μ D (productNormalizedSection μ T A z K f)))
        ≤ ∑ A ∈ T.powerset, K ^ A.card * B :=
      Finset.sum_le_sum (fun A hA => mul_le_mul_of_nonneg_left (hB A hA) (pow_nonneg hK.le _))
    _ = (1 + K) ^ T.card * B := by
      rw [← Finset.sum_mul]
      congr 1
      simpa only [Finset.prod_const] using (Finset.prod_one_add (f := fun _ : I => K) T).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

omit μ [∀ i, Fintype (X i)] in
theorem mem_disjointCoordinateLevel (T U : Finset I) (d : ℕ) :
    U ∈ disjointCoordinateLevel T d ↔ Disjoint T U ∧ U.card = d := by
  simp only [disjointCoordinateLevel, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_univ, true_and, and_comm]

theorem productANOVASectionTensor_energy (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    finiteProductIntegral (fun _ : Fin d => coordinateUnionWeight μ)
      (fun v => productANOVASectionTensor μ T d z base f v ^ 2) =
        productANOVASectionEnergy μ T (disjointCoordinateLevel T d) z f := by
  unfold productANOVASectionTensor
  rw [orderedFamilyTensor_energy μ]
  · simp only [productANOVASectionEnergy, disjointCoordinateLevel, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro U _
    by_cases hTU : Disjoint T U
    · simp only [hTU, ite_true]
    · simp only [hTU, ite_false, zero_pow (by decide : 2 ≠ 0), FiniteProbabilityWeights.mean_const]
  · intro U
    by_cases hTU : Disjoint T U
    · simpa only [hTU, ite_true] using (productANOVA_depends μ (T ∪ U) f).mix z
    · intro x y _
      simp only [hTU, ite_false]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVASectionTensor_bound_of_normalized_s2_oai (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) {K B : ℝ} (hK : 0 < K) (f : (∀ i, X i) → ℝ)
    (hLower : ∀ A ⊆ T,
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard d)
        (productNormalizedSection μ T A z K f)) ≤ B) :
    Real.sqrt (finiteProductIntegral (fun _ : Fin d => coordinateUnionWeight μ)
      (fun v => productANOVASectionTensor μ T d z base f v ^ 2)) ≤ (1 + K) ^ T.card * B := by
  rw [productANOVASectionTensor_energy]
  apply sqrt_productANOVASectionEnergy_le_of_normalized μ T (disjointCoordinateLevel T d)
    (fun U hU => ((mem_disjointCoordinateLevel T U d).mp hU).1) z hK f
  intro A hA
  apply (Real.sqrt_le_sqrt (productANOVAEnergy_le_level μ (disjointCoordinateLevel T d) d
    (fun U hU => ((mem_disjointCoordinateLevel T U d).mp hU).2)
    (productNormalizedSection μ T A z K f))).trans
  exact hLower A (Finset.mem_powerset.mp hA)

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.productANOVASectionTensor_bound_of_normalized_s2_oai.{u_1, u_2} := @OAI.Erdos3.productANOVASectionTensor_bound_of_normalized_s2_oai.{u_1, u_2}
