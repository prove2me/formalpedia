-- Prove2me | solution 1 for OAI.Erdos3.global_cutoff_initial_atom_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:16:34.867565+00:00
-- url     : https://prove2.me/submissions/8ce41d49-9f6c-4c39-a524-a4b96daa2c96

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_affine_masked_initial_conditioning_shell_small_s2
import Theorems.Thm_OAI_Erdos3_residue_source_stable_affine_comparison_at_degree_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedCoreBudget
namespace OAI

section

namespace Erdos3

theorem retained_core_allowance_spec {ε : ℝ} (hε : 0 < ε) :
    0 < ε / (2 + ε) ∧ ε / (2 + ε) ≤ 1 ∧ (ε / (2 + ε)) * (2 + ε) ≤ ε := by
  have hd : 0 < 2 + ε := by linarith
  refine ⟨div_pos hε hd, (div_le_one hd).mpr (by linarith), ?_⟩
  exact le_of_eq (div_mul_cancel₀ ε hd.ne')

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

theorem productAtomTruncatedPairing_sub_smul_right (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) (a : ℝ) (w : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ) :
    productAtomTruncatedPairing c D I x y w (fun z => f z - a * g z) =
      productAtomTruncatedPairing c D I x y w f - a * productAtomTruncatedPairing c D I x y w g := by
  have he : (fun z => productFiberIndicator I y z * (f z - a * g z)) =
      (fun z => productFiberIndicator I y z * f z - a * (productFiberIndicator I y z * g z)) := by
    funext z
    ring
  change productTruncatedPairing c D (fun z => productFiberIndicator I x z * w z) _ = _
  rw [he, productTruncatedPairing_sub_smul_right]
  rfl

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

section

namespace Erdos3

open scoped Classical

theorem affineInitialPrimeMask_contains {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM : ℕ) :
    affineMandatoryPrimes prime ξ P ⊆ affineInitialPrimeMask prime ξ P sourceM siteM ∧
    periodPrimeCoordinates prime sourceM ⊆ affineInitialPrimeMask prime ξ P sourceM siteM ∧
    periodPrimeCoordinates prime siteM ⊆ affineInitialPrimeMask prime ξ P sourceM siteM := by
  exact ⟨Finset.subset_union_left.trans Finset.subset_union_left,
    Finset.subset_union_right.trans Finset.subset_union_left, Finset.subset_union_right⟩

theorem affineInitialPrimeMask_outside_coprime {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    {ξ P : ℝ} {sourceM siteM : ℕ} (K : Finset ι)
    (hK : affineInitialPrimeMask prime ξ P sourceM siteM ⊆ K)
    (i : ι) (hi : i ∉ K) :
    sourceM.Coprime (prime i ^ power i) ∧ siteM.Coprime (prime i ^ power i) := by
  have hcontains := affineInitialPrimeMask_contains prime ξ P sourceM siteM
  have hcop (M : ℕ) (hM : periodPrimeCoordinates prime M ⊆ K) : M.Coprime (prime i ^ power i) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (hprime i).coprime_iff_not_dvd.mpr
    intro hd
    exact hi (hM ((mem_periodPrimeCoordinates prime M i).mpr hd))
  exact ⟨hcop sourceM (hcontains.2.1.trans hK), hcop siteM (hcontains.2.2.trans hK)⟩

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem affineSamplerPrimeMask_contains {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM D : ℕ) :
    affineInitialPrimeMask prime ξ P sourceM siteM ⊆
      affineSamplerPrimeMask prime ξ P sourceM siteM D ∧
    periodPrimeCoordinates prime D ⊆ affineSamplerPrimeMask prime ξ P sourceM siteM D :=
  ⟨Finset.subset_union_left, Finset.subset_union_right⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StableReferenceMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedCombined_coprime_outside {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hpair : Pairwise (fun i j => (q i).Coprime (q j))) (M : ℕ) (K : Finset ι)
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (j : ι) (hj : j ∉ K) :
    (M.lcm (∏ i ∈ K, q i)).Coprime (q j) := by
  have hK : (∏ i ∈ K, q i).Coprime (q j) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    exact hpair (fun heq => hj (heq ▸ hi))
  exact Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul M _)
    (Nat.coprime_mul_iff_left.mpr ⟨hcop j hj, hK⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCellNormLengths
namespace OAI

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

omit hne hpair in
theorem residuePrimeCoordinateMassRatio_pos : 0 < residuePrimeCoordinateMassRatio lo N M a q K base := by
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base) := ⟨u⟩
  let : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) := ⟨u.val⟩
  have hp : 0 < ∏ i ∈ K, q i := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))
  rw [residuePrimeCoordinateMassRatio_eq_count]
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.InitialMaskedAffineComparison
namespace OAI

section

namespace Erdos3

theorem affineComparisonAccuracyLog_mono_degree {b B : ℕ} {P L T : ℝ}
    (hb : b ≤ B) (hP : 0 ≤ P) :
    affineComparisonAccuracyLog b P L T ≤ affineComparisonAccuracyLog B P L T := by
  unfold affineComparisonAccuracyLog
  gcongr

theorem affineComparisonRequiredOrder_mono {b B : ℕ} (hb : b ≤ B) (ε L T C : ℝ) :
    affineComparisonRequiredOrder b ε L T C ≤ affineComparisonRequiredOrder B ε L T C := by
  unfold affineComparisonRequiredOrder
  omega

theorem affineComparisonRequiredOrder_two_mul (b : ℕ) (ε L T C : ℝ) :
    2 * b ≤ affineComparisonRequiredOrder b ε L T C := by
  unfold affineComparisonRequiredOrder
  omega

theorem affineComparisonLengthLog_mono_degree {b B : ℕ} {ε L T C modLog dimLog : ℝ}
    (hb : b ≤ B) (hP : 0 ≤ affineComparisonScale ε L T C) (hmodLog : 0 ≤ modLog) :
    affineComparisonLengthLog b ε L T C modLog dimLog ≤
      affineComparisonLengthLog B ε L T C modLog dimLog := by
  unfold affineComparisonLengthLog
  have ho : (affineComparisonRequiredOrder b ε L T C : ℝ) ≤
      (affineComparisonRequiredOrder B ε L T C : ℝ) := by
    exact_mod_cast affineComparisonRequiredOrder_mono hb ε L T C
  have ha := affineComparisonAccuracyLog_mono_degree (L := L) (T := T) hb hP
  have hm := mul_le_mul_of_nonneg_left ho hmodLog
  linarith

theorem affineComparisonLengthLog_initial {ε L T C modLog dimLog : ℝ} (B : ℕ)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hmodLog : 0 ≤ modLog) :
    modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B (affineComparisonScale ε L T C) 0 0 + dimLog + 1 ≤
      affineComparisonLengthLog B ε L T C modLog dimLog := by
  have ho : ((2 * B : ℕ) : ℝ) ≤ (affineComparisonRequiredOrder B ε L T C : ℝ) := by
    exact_mod_cast affineComparisonRequiredOrder_two_mul B ε L T C
  have ha : affineComparisonAccuracyLog B (affineComparisonScale ε L T C) 0 0 ≤
      affineComparisonAccuracyLog B (affineComparisonScale ε L T C) L T := by
    unfold affineComparisonAccuracyLog
    linarith
  have hm := mul_le_mul_of_nonneg_left ho hmodLog
  change _ ≤ _
  dsimp only [affineComparisonLengthLog]
  linarith

theorem affineGlobalCutoff_outside {A B n b : ℕ} (hn : n ≤ A) (hB : A + b ≤ B) :
    b ≤ B - n ∧ B - n ≤ B ∧ n ≤ B := by omega

theorem CyclicCrootSisask.spectralIterations_mono_budget {shell P Q : ℝ} (hPQ : P ≤ Q) :
    CyclicCrootSisask.spectralIterations shell P ≤ CyclicCrootSisask.spectralIterations shell Q := by
  unfold CyclicCrootSisask.spectralIterations
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem affineGlobalCutoff_initial {n A B : ℕ} {V W shell : ℝ}
    (hn : n ≤ A) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hB : A + CyclicCrootSisask.spectralIterations shell ((A : ℝ) * (V + W + 1) + 4) ≤ B) :
    n + CyclicCrootSisask.spectralIterations shell ((n : ℝ) * (V + W + 1) + 4) ≤ B := by
  have hn' : (n : ℝ) ≤ A := by exact_mod_cast hn
  have hp : (n : ℝ) * (V + W + 1) + 4 ≤ (A : ℝ) * (V + W + 1) + 4 := by gcongr
  have hs := CyclicCrootSisask.spectralIterations_mono_budget (shell := shell) hp
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.InitialMaskedAffineComparisonAtDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceBase : ∀ i, Option J × σ → ZMod (q i))
variable (sourceCell : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase)
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase,
  0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (hsourceCop : ∀ i ∉ K, sourceM.Coprime (q i))
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * b + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (b)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

include hb hstable hupper hM hpair hcop u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM hsourceCop sourceDimLog hsourceDim hsourceLength

theorem conditioned_source_stable_affine_comparison_at_degree :
    let density := fun f => residueCellOutsideDensity lo N M a q K base u f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  let e := residuePrimeCoordinateCell_lcmEquiv sourceLo sourceN sourceM sourceA q hpair K sourceBase sourceCell
  have hQ : 0 < sourceM.lcm (∏ i ∈ K, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hsourceM.ne'
      (Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))).ne')
  have hQcop : ∀ i ∉ K, (sourceM.lcm (∏ k ∈ K, q k)).Coprime (q i) :=
    fun i hi => selectedCombined_coprime_outside q hpair sourceM K hsourceCop i hi
  have hw' (z : IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
      (fun _ => (sourceM.lcm (∏ i ∈ K, q i) : ℤ)) (fun k => (sourceCell.val k).val)) :
      0 ≤ w (fun k => (z k).val) ∧ w (fun k => (z k).val) ≤ 1 :=
    hw (e.symm z)
  have result := residue_source_stable_affine_comparison_at_degree_s2 (b := b) (hb := hb) (ι := ι) (σ := σ) (J := J)
    (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (ε := ε) (L := L) (T := T) (C := C) (shell := shell) (modLog := modLog)
    (level := level) (K := K) (base := base)
    (hstable := hstable) (hupper := hupper) (hM := hM) (hpair := hpair) (hcop := hcop)
    (u := u) (hg := hg) (hh := hh) (hL := hL) (hT := hT) (hlower := hlower)
    (prime := prime) (power := power) (hprime := hprime) (hpower := hpower) (hJ := hJ)
    (hshell := hshell) (hlevel2 := hlevel2) (hmodLog := hmodLog) (hmoduli := hmoduli)
    (hε := hε) (hC := hC) (hcount := hcount) (hmandatory := hmandatory)
    (dimLog := dimLog) (hdim := hdim) (hlength := hlength)
    (sourceLo := sourceLo) (sourceN := sourceN) (sourceM := sourceM.lcm (∏ i ∈ K, q i))
    (sourceA := fun k => (sourceCell.val k).val)
    (sourceNonempty := residuePrimeCoordinateCell_lcm_nonempty sourceLo sourceN sourceM sourceA q hpair K sourceBase sourceCell)
    (w := w) (hw := hw') (hsourceM := hQ) (hsourceCop := hQcop)
    (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim) (hsourceLength := hsourceLength)
  have hsrc := residueCellOutsideDensity_lcm sourceLo sourceN sourceM sourceA q hpair K sourceBase sourceCell w
  have hsiteH := residueCellOutsideDensity_lcm lo N M a q hpair K base u (fun x => (h x).re)
  have hsiteG := residueCellOutsideDensity_lcm lo N M a q hpair K base u (fun x => (g x).re)
  have htest := congrArg₂
    (fun f g : (∀ i : {i // i ∉ K}, σ → ZMod (q i.val)) → ℝ =>
      fun z => f z - (1 + ε) * level * g z) hsiteH hsiteG
  have heq := congrArg₂
    (affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K}
        (b)))
    hsrc htest
  exact heq.trans_le result

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceBase : ∀ i, Option J × σ → ZMod (q i))
variable (sourceCell : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase)
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase,
  0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * b + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (b)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

variable (hinj : Function.Injective prime)
variable (hmask : affineInitialPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M ⊆ K)

include hb hstable hupper hM u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM sourceDimLog hsourceDim hsourceLength hinj hmask

theorem initial_masked_affine_comparison_at_degree :
    let density := fun f => residueCellOutsideDensity lo N M a q K base u f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  have hpair : Pairwise (fun i k => (q i).Coprime (q k)) := by
    intro i k hik
    rw [hpower i, hpower k]
    exact selectedPrimePowers_pairwise_coprime prime power hprime hinj hik
  have hboth := affineInitialPrimeMask_outside_coprime (ι := ι) prime power hprime
    (ξ := ε / (2 + ε)) (P := affineComparisonScale ε L T C) (sourceM := sourceM) (siteM := M) K hmask
  have hcop : ∀ i ∉ K, M.Coprime (q i) := by
    intro i hi
    rw [hpower i]
    exact (hboth i hi).2
  have hsourceCop : ∀ i ∉ K, sourceM.Coprime (q i) := by
    intro i hi
    rw [hpower i]
    exact (hboth i hi).1
  have hmandatory :=
    (affineInitialPrimeMask_contains prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M).1.trans hmask
  exact conditioned_source_stable_affine_comparison_at_degree (b := b) (hb := hb)
    (ι := ι) (σ := σ) (J := J) (h := h)
    (g := g) (lo := lo) (a := a) (N := N)
    (M := M) (q := q) (ε := ε) (L := L)
    (T := T) (C := C) (shell := shell) (modLog := modLog)
    (level := level) (K := K) (base := base) (hstable := hstable)
    (hupper := hupper) (hM := hM) (hpair := hpair) (hcop := hcop)
    (u := u) (hg := hg) (hh := hh) (hL := hL)
    (hT := hT) (hlower := hlower) (prime := prime) (power := power)
    (hprime := hprime) (hpower := hpower) (hJ := hJ) (hshell := hshell)
    (hlevel2 := hlevel2) (hmodLog := hmodLog) (hmoduli := hmoduli) (hε := hε)
    (hC := hC) (hcount := hcount) (hmandatory := hmandatory) (dimLog := dimLog)
    (hdim := hdim) (hlength := hlength) (sourceLo := sourceLo) (sourceN := sourceN)
    (sourceM := sourceM) (sourceA := sourceA) (sourceBase := sourceBase) (sourceCell := sourceCell)
    (w := w) (hw := hw) (hsourceM := hsourceM) (hsourceCop := hsourceCop)
    (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim) (hsourceLength := hsourceLength)

end

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.GlobalCutoffAffineComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {A B : ℕ}
variable (hKcard : K.card ≤ A)
variable (hB : A + affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ B)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (affineComparisonLengthLog B ε L T C modLog dimLog) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceBase : ∀ i, Option J × σ → ZMod (q i))
variable (sourceCell : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase)
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase,
  0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (affineComparisonLengthLog B ε L T C modLog sourceDimLog) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

variable (hinj : Function.Injective prime)
variable (hmask : affineInitialPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M ⊆ K)

include hKcard hB hstable hupper hM u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM sourceDimLog hsourceDim hsourceLength hinj hmask

theorem global_cutoff_masked_affine_comparison :
    let density := fun f => residueCellOutsideDensity lo N M a q K base u f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card)) (residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have hdegree := affineGlobalCutoff_outside hKcard hB
  have hlength' (k : σ) : Real.exp (affineComparisonLengthLog (B - K.card) ε L T C modLog dimLog) ≤
      (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ) :=
    (Real.exp_le_exp.mpr (affineComparisonLengthLog_mono_degree hdegree.2.1 hP hmodLog)).trans (hlength k)
  have hsourceLength' (k : Option J × σ) :
      Real.exp (affineComparisonLengthLog (B - K.card) ε L T C modLog sourceDimLog) ≤
      (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ) :=
    (Real.exp_le_exp.mpr (affineComparisonLengthLog_mono_degree hdegree.2.1 hP hmodLog)).trans (hsourceLength k)
  exact initial_masked_affine_comparison_at_degree (b := B - K.card) (hb := hdegree.1)
    (ι := ι) (σ := σ) (J := J) (h := h) (g := g) (lo := lo) (a := a) (N := N)
    (M := M) (q := q) (ε := ε) (L := L) (T := T) (C := C) (shell := shell)
    (modLog := modLog) (level := level) (K := K) (base := base)
    (hstable := hstable) (hupper := hupper) (hM := hM) (u := u) (hg := hg) (hh := hh)
    (hL := hL) (hT := hT) (hlower := hlower) (prime := prime) (power := power)
    (hprime := hprime) (hpower := hpower) (hJ := hJ) (hshell := hshell) (hlevel2 := hlevel2)
    (hmodLog := hmodLog) (hmoduli := hmoduli) (hε := hε) (hC := hC) (hcount := hcount)
    (dimLog := dimLog) (hdim := hdim) (hlength := hlength')
    (sourceLo := sourceLo) (sourceA := sourceA) (sourceN := sourceN) (sourceM := sourceM)
    (sourceBase := sourceBase) (sourceCell := sourceCell) (w := w) (hw := hw)
    (hsourceM := hsourceM) (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim)
    (hsourceLength := hsourceLength') (hinj := hinj) (hmask := hmask)

end

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GlobalCutoffAtomComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {A B : ℕ}
variable (hKcard : K.card ≤ A)
variable (hB : A + affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ B)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (affineComparisonLengthLog B ε L T C modLog dimLog) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceBase : ∀ i, Option J × σ → ZMod (q i))
variable (sourceCell : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase)
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase,
  0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (affineComparisonLengthLog B ε L T C modLog sourceDimLog) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

variable (hinj : Function.Injective prime)
variable (D : ℕ) (parameterA : J → ℤ)
variable (hmask : affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M D ⊆ K)
variable (hBinitial : A + CyclicCrootSisask.spectralIterations shell
  ((A : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B)

include D parameterA hBinitial hKcard hB hstable hupper hM u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM sourceDimLog hsourceDim hsourceLength hinj hmask

theorem global_cutoff_initial_atom_comparison_s2_oai :
    let c := affinePeriodProductCoupling (σ := σ) q D parameterA
    let source := residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA ⟨sourceCell.val⟩ q w
    let site := fun f => residuePrimeCoordinateDensity lo N M a ⟨u.val⟩ q f
    let factor := productCouplingAtomMass c K sourceBase base *
      (residuePrimeCoordinateMassRatio sourceLo sourceN sourceM sourceA q K sourceBase *
        residuePrimeCoordinateMassRatio lo N M a q K base)
    productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K sourceBase base source
      (fun z => site (fun x => (h x).re) z - (1 + ε) * level * site (fun x => (g x).re) z) ≤
      factor * (level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
        Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)) +
      (1 + (1 + ε) * level) * (shell / 16) := by
  let c := affinePeriodProductCoupling (σ := σ) q D parameterA
  let source := residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA ⟨sourceCell.val⟩ q w
  let site := fun f => residuePrimeCoordinateDensity lo N M a ⟨u.val⟩ q f
  let sourceOut := residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w
  let siteOut := fun f => residueCellOutsideDensity lo N M a q K base u f
  let full := fun f => productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K sourceBase base source (site f)
  let core := fun f => affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card)) sourceOut (siteOut f)
  let ratioX := residuePrimeCoordinateMassRatio sourceLo sourceN sourceM sourceA q K sourceBase
  let ratioY := residuePrimeCoordinateMassRatio lo N M a q K base
  let mass := productCouplingAtomMass c K sourceBase base
  let factor := mass * (ratioX * ratioY)
  let coeff := (1 + ε) * level
  let R := level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
    Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have hcountP := affineComparisonScale_count (ι := ι) (ε := ε) hL hT hC hcount
  have hxi := (retained_core_allowance_spec hε).1
  have hmaskBase := (affineSamplerPrimeMask_contains prime (ε / (2 + ε))
    (affineComparisonScale ε L T C) sourceM M D).1.trans hmask
  have hlocal := global_cutoff_masked_affine_comparison (hKcard := hKcard) (hB := hB)
    (ι := ι) (σ := σ) (J := J) (h := h) (g := g) (lo := lo) (a := a) (N := N)
    (M := M) (q := q) (ε := ε) (L := L) (T := T) (C := C) (shell := shell)
    (modLog := modLog) (level := level) (K := K) (base := base)
    (hstable := hstable) (hupper := hupper) (hM := hM) (u := u) (hg := hg) (hh := hh)
    (hL := hL) (hT := hT) (hlower := hlower) (prime := prime) (power := power)
    (hprime := hprime) (hpower := hpower) (hJ := hJ) (hshell := hshell) (hlevel2 := hlevel2)
    (hmodLog := hmodLog) (hmoduli := fun i _ => hmoduli i) (hε := hε) (hC := hC) (hcount := hcount)
    (dimLog := dimLog) (hdim := hdim) (hlength := hlength)
    (sourceLo := sourceLo) (sourceA := sourceA) (sourceN := sourceN) (sourceM := sourceM)
    (sourceBase := sourceBase) (sourceCell := sourceCell) (w := w) (hw := hw)
    (hsourceM := hsourceM) (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim)
    (hsourceLength := hsourceLength) (hinj := hinj) (hmask := hmaskBase)
  dsimp only at hlocal
  simp only [affineResidueTruncatedPairing, productTruncatedPairing_sub_smul_right] at hlocal
  change core (fun x => (h x).re) - coeff * core (fun x => (g x).re) ≤ R at hlocal
  have hlengthInitial (k : σ) :
      Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B (affineComparisonScale ε L T C) 0 0 + dimLog + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ) :=
    (Real.exp_le_exp.mpr (affineComparisonLengthLog_initial (ε := ε) (C := C) B hL hT hmodLog)).trans (hlength k)
  have hsourceLengthInitial (k : Option J × σ) :
      Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B (affineComparisonScale ε L T C) 0 0 + sourceDimLog + 1) ≤
      (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ) :=
    (Real.exp_le_exp.mpr (affineComparisonLengthLog_initial (ε := ε) (C := C) B hL hT hmodLog)).trans (hsourceLength k)
  have hcut := affineGlobalCutoff_initial hKcard
    (by positivity : 0 ≤ (Fintype.card (Option J × σ) : ℝ) * modLog)
    (by positivity : 0 ≤ (Fintype.card σ : ℝ) * modLog) hBinitial
  have herror (f : (σ → ℤ) → ℝ)
      (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1) :
      |full f - factor * core f| ≤ shell / 16 := by
    have hcell (z : ResiduePrimeCoordinateCell lo N M a q K base) :
        0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1 := by
      apply hf
      apply (mem_translatedIntegerBox lo N _).mpr
      intro k
      exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z.val k).property).1)
    have hs := affine_masked_initial_conditioning_shell_small_s2
      sourceLo sourceN sourceM sourceA ⟨sourceCell.val⟩ lo N M a ⟨u.val⟩ q K sourceBase base sourceCell u
      D parameterA prime power hprime hpower hinj hJ w f B hsourceM hM hw hcell
      (affineComparisonScale ε L T C) modLog sourceDimLog dimLog hP hmodLog
      (ε / (2 + ε)) hxi hmask hcountP hmoduli hsourceDim hdim
      hsourceLengthInitial hlengthInitial shell hshell hcut
    change |full f - mass * (ratioX * ratioY * core f)| ≤ shell / 16 at hs
    simpa only [factor, mul_assoc] using hs
  have hH := (abs_le.mp (herror (fun x => (h x).re) hh)).2
  have hG := (abs_le.mp (herror (fun x => (g x).re) hg)).1
  have hcoeff : 0 ≤ coeff := mul_nonneg (by linarith only [hε]) ((Real.exp_pos (-L)).le.trans hlower)
  have hfactor : 0 ≤ factor := mul_nonneg (productCouplingAtomMass_nonneg c K sourceBase base)
    (mul_nonneg (residuePrimeCoordinateMassRatio_pos sourceLo sourceN sourceM sourceA q K sourceBase sourceCell).le
      (residuePrimeCoordinateMassRatio_pos lo N M a q K base u).le)
  have hG' := mul_le_mul_of_nonneg_left hG hcoeff
  have hlocal' := mul_le_mul_of_nonneg_left hlocal hfactor
  change productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K sourceBase base source
    (fun z => site (fun x => (h x).re) z - coeff * site (fun x => (g x).re) z) ≤ factor * R + (1 + coeff) * (shell / 16)
  rw [productAtomTruncatedPairing_sub_smul_right]
  change full (fun x => (h x).re) - coeff * full (fun x => (g x).re) ≤ factor * R + (1 + coeff) * (shell / 16)
  nlinarith only [hH, hG', hlocal']

end

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.global_cutoff_initial_atom_comparison_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.global_cutoff_initial_atom_comparison_s2_oai.{u_1, u_2, u_3}
