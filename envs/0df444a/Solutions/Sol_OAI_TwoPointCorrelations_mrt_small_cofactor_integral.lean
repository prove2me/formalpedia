-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_small_cofactor_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:38:31.278415+00:00
-- url     : https://prove2.me/submissions/61964e4b-7e42-4d2e-8e06-fc42a9784ef1

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_integer_kernel_on_samples

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped _root_.BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]



omit [DecidableEq α] [LinearOrder ι] in
@[simp] theorem mem_survivors {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α} :
    x ∈ survivors C P bad ↔ x ∈ C ∧ ∀ p ∈ P, ¬ bad p x := by
  classical
  simp [survivors]











instance decidableResidueBad (a : ℕ → ℕ) (p n : ℕ) : Decidable (residueBad a p n) :=
  inferInstanceAs (Decidable (n % p = a p % p))






end NumberTheoryLean.SievePartition

end

section

namespace NumberTheoryLean.SieveTree

open scoped _root_.BigOperators

variable {V : Type*} [DecidableEq V]








end NumberTheoryLean.SieveTree

end

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped _root_.BigOperators
open _root_.OAI.Erdos970.NumberTheoryLean.SievePartition

















end NumberTheoryLean.ResidueSieveTree

end

section

namespace ErdosInverseCounts
open _root_.OAI.Erdos970.NumberTheoryLean _root_.OAI.Erdos970.NumberTheoryLean.SievePartition









end ErdosInverseCounts

end

section

namespace ErdosAlignedProgression






end ErdosAlignedProgression

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.LargePrimeDeletion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped _root_.BigOperators






@[simp] theorem mem_deletionCell {C : Finset ℕ} {a : ℤ} {q i : ℕ} :
    i ∈ deletionCell C a q ↔ i ∈ C ∧ (q : ℤ) ∣ a + i := by
  classical
  simp [deletionCell]







@[simp] theorem mem_cutoffSurvivors {Y z i : ℕ} {residue : ℕ → ℕ} :
    i ∈ cutoffSurvivors Y z residue ↔
      i < Y ∧ ∀ p, p.Prime → p ≤ z → i % p ≠ residue p % p := by
  classical
  simp only [cutoffSurvivors, SievePartition.mem_survivors, Finset.mem_range,
    mem_cutoffPrimes, SievePartition.residueBad]
  tauto





@[simp] theorem mem_coprimeOffsets {Y n i : ℕ} {a : ℤ} :
    i ∈ coprimeOffsets Y n a ↔ i < Y ∧ (a + i).natAbs.Coprime n := by
  classical
  simp [coprimeOffsets]









end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.IntervalBoundingSieve
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.IntervalBoundingSieve

open scoped _root_.BigOperators
















@[simp] theorem cutoffProduct_primeFactors (z : ℕ) :
    (cutoffProduct z).primeFactors = LargePrimeDeletion.cutoffPrimes z := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1


end NumberTheoryLean.IntervalBoundingSieve

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniDensity

open scoped _root_.BigOperators


@[simp] theorem elementarySum_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    elementarySum P g 0 = 1 := by simp [elementarySum]











@[simp] theorem densityPolynomial_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial 0 P g = 1 := by simp [densityPolynomial]









end NumberTheoryLean.BonferroniDensity

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.DisjointBlockExpansion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DisjointBlockExpansion

open scoped _root_.BigOperators


@[simp] theorem mem_blockChoices {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {choice : ∀ j ∈ B, Finset ℕ} :
    choice ∈ blockChoices B blocks ↔ ∀ j (hj : j ∈ B), choice j hj ⊆ blocks j := by
  classical
  simp only [blockChoices, Finset.mem_pi, Finset.mem_powerset]






















@[simp] theorem truncatedCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    truncatedCoefficient m T ≠ 0 ↔ T.card ≤ m := by
  unfold truncatedCoefficient
  split_ifs <;> simp_all

@[simp] theorem layerCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    layerCoefficient m T ≠ 0 ↔ T.card = m := by
  unfold layerCoefficient
  split_ifs <;> simp_all


























end NumberTheoryLean.DisjointBlockExpansion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.SquarefreeHarmonic
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped _root_.BigOperators _root_.ArithmeticFunction.Moebius




























end NumberTheoryLean.SelbergOptimization

end

section

namespace NumberTheoryLean.SquarefreeHarmonic

open scoped _root_.BigOperators


@[simp] theorem mem_squarefreeUpTo {R d : ℕ} :
    d ∈ squarefreeUpTo R ↔ 1 ≤ d ∧ d ≤ R ∧ Squarefree d := by
  classical
  simp only [squarefreeUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto
















end NumberTheoryLean.SquarefreeHarmonic

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.PrimeDensityBlocks
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped _root_.BigOperators


@[simp] theorem mem_dyadicPrimes {n p : ℕ} :
    p ∈ dyadicPrimes n ↔ n ≤ p ∧ p < 2 * n ∧ p.Prime := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto






@[simp] theorem mem_geometricPrimes {j p : ℕ} :
    p ∈ geometricPrimes j ↔ 2 ^ (2 ^ j) ≤ p ∧ p < 2 ^ (2 ^ (j + 1)) ∧ p.Prime := by
  simp only [geometricPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto





















end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LocalFactors
namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations


@[simp] theorem fromPrimePowers_one (F : ℕ → ℕ → ℂ) : fromPrimePowers F 1 = 1 := by
  simp [fromPrimePowers]



@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcPacking
namespace OAI

/-! Elementary interval packing for separated phase representatives. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_interval_packing {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (δ b : ℝ) (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|) :
    (S.filter (fun i => b ≤ x i ∧ x i < b + δ)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiS, hix⟩ := mem_filter.mp hi
  obtain ⟨hjS, hjx⟩ := mem_filter.mp hj
  by_contra hij
  have hh := hsep i hiS j hjS hij
  have habs : |x i - x j| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

lemma minor_arc_absolute_band_packing {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (δ b : ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|) :
    (S.filter (fun i => b ≤ |x i| ∧ |x i| < b + δ)).card ≤ 2 := by
  let P := S.filter (fun i => b ≤ x i ∧ x i < b + δ)
  let Q := S.filter (fun i => b ≤ -x i ∧ -x i < b + δ)
  have hP : P.card ≤ 1 := minor_arc_interval_packing S x δ b hsep
  have hQ : Q.card ≤ 1 := by
    apply minor_arc_interval_packing S (fun i => -x i) δ b
    intro i hi j hj hij
    simpa only [neg_sub_neg, abs_sub_comm] using hsep i hi j hj hij
  have hsub : S.filter (fun i => b ≤ |x i| ∧ |x i| < b + δ) ⊆ P ∪ Q := by
    intro i hi
    obtain ⟨hiS, hix⟩ := mem_filter.mp hi
    by_cases hx : 0 ≤ x i
    · apply mem_union_left
      exact mem_filter.mpr ⟨hiS, by simpa only [abs_of_nonneg hx] using hix⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨hiS, by simpa only [abs_of_neg (lt_of_not_ge hx)] using hix⟩
  have hu := (card_le_card hsub).trans (card_union_le P Q)
  omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquareRows
namespace OAI

/-! Summable quadratic-gap bounds for the MRT Dirichlet mean-value estimate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.BigOperators


lemma mrt_quadratic_gap_sum {R : ℝ} (hR : 0 < R) (N : ℕ) :
    (∑ k ∈ Ioc 0 N, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ 2 * R + 1 := by
  let K := Nat.ceil R
  let M := max K N
  have hK : 0 < K := Nat.ceil_pos.mpr hR
  have hRK : R ≤ (K : ℝ) := Nat.le_ceil R
  have hKR : (K : ℝ) < R + 1 := Nat.ceil_lt_add_one hR.le
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hKM : K ≤ M := le_max_left _ _
  have hsplit : Ioc 0 M = Ioc 0 K ∪ Ioc K M := by
    ext k
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 K) (Ioc K M) := by
    rw [disjoint_left]
    simp only [mem_Ioc]
    omega
  have hnear : (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Ioc 0 K, (1 : ℝ) := by
        apply sum_le_sum
        intro k _
        exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((k : ℝ) / R)])
      _ = _ := by simp
  have hfar : (∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ R := by
    calc
      _ ≤ ∑ k ∈ Ioc K M, R ^ 2 * ((k : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (hK.trans (mem_Ioc.mp hk).1)
        calc
          _ ≤ (((k : ℝ) / R) ^ 2)⁻¹ := by
            apply inv_anti₀ (sq_pos_of_pos (div_pos hk0 hR))
            linarith
          _ = _ := by field_simp
      _ = R ^ 2 * ∑ k ∈ Ioc K M, ((k : ℝ) ^ 2)⁻¹ := (mul_sum _ _ _).symm
      _ ≤ R ^ 2 * ((K : ℝ)⁻¹ - (M : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (α := ℝ) hK.ne' hKM)
          (sq_nonneg R)
      _ ≤ R ^ 2 * (K : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg M))
      _ ≤ R := by
        rw [← div_eq_mul_inv, div_le_iff₀ hK0]
        nlinarith
  calc
    _ ≤ ∑ k ∈ Ioc 0 M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [mem_Ioc] at hk ⊢
        exact ⟨hk.1, hk.2.trans (le_max_right _ _)⟩
      · intro k _ _
        positivity
    _ = (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) +
        ∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by rw [hsplit, sum_union hd]
    _ ≤ (K : ℝ) + R := add_le_add hnear hfar
    _ ≤ 2 * R + 1 := by linarith




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare
namespace OAI

/-! Finite Dirichlet-polynomial mean squares, using the integrable
exponential majorant and its exact quadratic-decay Fourier transform. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.BigOperators _root_.ComplexConjugate


lemma mrt_phase_pair (x y : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) *
        conj (Complex.exp ((y : ℂ) * Complex.I)) =
      Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, ofReal_sub]
  ring










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWeightedMeanSquare
namespace OAI

/-! Weighted Schur estimates for the prime-supported polynomials in Halász's
mean-value argument.  The weight occurs only once in the squared coefficient
sum, so a bound for the weighted frequency rows saves the extra logarithm
that an unrestricted integer mean-value theorem would lose. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators _root_.Classical

lemma halasz_weighted_symmetric_row_bound {ι : Type*} (S : Finset ι)
    (K : ι → ι → ℝ) (w v : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, w j * K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, (v i * w i) * (v j * w j) * K i j) ≤
      C * ∑ i ∈ S, (v i) ^ 2 * w i := by
  have he : (∑ i ∈ S, ∑ j ∈ S,
      ((v i) ^ 2 + (v j) ^ 2) / 2 * (w i * w j * K i j)) =
      ∑ i ∈ S, (v i) ^ 2 * w i * ∑ j ∈ S, w j * K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S)
      (f := fun i j => (v j) ^ 2 / 2 * (w i * w j * K i j))]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [hsymm j hj i hi]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S,
        ((v i) ^ 2 + (v j) ^ 2) / 2 * (w i * w j * K i j) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hv : v i * v j ≤ ((v i) ^ 2 + (v j) ^ 2) / 2 := by
        nlinarith [sq_nonneg (v i - v j)]
      convert (preTransparency := .instances) mul_le_mul_of_nonneg_right hv
        (mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hK i hi j hj)) using 1; ring
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * w i * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (mul_nonneg (sq_nonneg _) (hw i hi))
    _ = _ := by rw [← sum_mul, mul_comm]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiplicativeReduction
namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical








@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]






@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := if_neg hn.ne'




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseGram
namespace OAI

/-! Finite duality for sparse Dirichlet-polynomial samples.  The analytic
input is an explicit Gram-row sum, with no density-to-energy substitution. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.ComplexConjugate

lemma mrt_gram_synthesis {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (a : ι → ℂ)
    {B : ℝ} (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    ‖∑ i ∈ S, a i • v i‖^2 ≤ B * ∑ i ∈ S, ‖a i‖^2 := by
  calc
    _ = (inner ℂ (∑ i ∈ S, a i • v i) (∑ i ∈ S, a i • v i)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ ≤ ‖inner ℂ (∑ i ∈ S, a i • v i) (∑ i ∈ S, a i • v i)‖ := re_le_norm _
    _ = ‖∑ i ∈ S, ∑ j ∈ S, conj (a i) * a j * inner ℂ (v i) (v j)‖ := by
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_sum]
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖conj (a i) * a j * inner ℂ (v i) (v j)‖ := by
      exact (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ = ∑ i ∈ S, ∑ j ∈ S,
        (‖a i‖ * 1) * (‖a j‖ * 1) * ‖inner ℂ (v i) (v j)‖ := by
      simp only [norm_mul, norm_conj, mul_one]
    _ ≤ B * ∑ i ∈ S, ‖a i‖^2 := by
      simpa only [mul_one] using halasz_weighted_symmetric_row_bound S
        (fun i j => ‖inner ℂ (v i) (v j)‖) (fun _ => 1) (fun i => ‖a i‖) B
        (fun _ _ => by norm_num) (fun _ _ _ _ => norm_nonneg _)
        (fun i _ j _ => norm_inner_symm _ _) (by simpa only [one_mul] using hrow)

/-- Finite Bessel inequality with an absolute Gram-row bound. -/
theorem mrt_gram_analysis {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (u : E)
    {B : ℝ} (hB : 0 ≤ B) (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    (∑ i ∈ S, ‖inner ℂ (v i) u‖^2) ≤ B * ‖u‖^2 := by
  let b := fun i => inner ℂ (v i) u
  let z := ∑ i ∈ S, b i • v i
  let A := ∑ i ∈ S, ‖b i‖^2
  have hA : 0 ≤ A := sum_nonneg (fun _ _ => sq_nonneg _)
  have hz : inner ℂ z u = (A : ℂ) := by
    dsimp only [z, A]
    rw [sum_inner]
    push_cast
    apply sum_congr rfl
    intro i _
    rw [inner_smul_left]
    exact conj_mul' (b i)
  have hc : A ≤ ‖z‖ * ‖u‖ := by
    calc
      A = ‖inner ℂ z u‖ := by rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
      _ ≤ _ := norm_inner_le_norm _ _
  have hz2 : ‖z‖^2 ≤ B*A := mrt_gram_synthesis S v b hrow
  have hc2 : A^2 ≤ ‖z‖^2 * ‖u‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hA hc 2
  have hprod := mul_le_mul_of_nonneg_right hz2 (sq_nonneg ‖u‖)
  by_cases hAz : A = 0
  · change A ≤ B * ‖u‖^2
    rw [hAz]
    exact mul_nonneg hB (sq_nonneg _)
  · change A ≤ B * ‖u‖^2
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    apply (mul_le_mul_iff_right₀ hApos).mp
    calc
      A * A = A^2 := by ring
      _ ≤ B * A * ‖u‖^2 := hc2.trans hprod
      _ = A * (B * ‖u‖^2) := by ring

/-- The Gram kernel is evaluated on the actual coefficient matrix. -/
theorem mrt_finite_matrix_gram {ι κ : Type*} (S : Finset ι) (K : Finset κ)
    (A : ι → κ → ℂ) (a : κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖∑ n ∈ K, A i n * conj (A j n)‖ ≤ B) :
    (∑ i ∈ S, ‖∑ n ∈ K, A i n * a n‖^2) ≤ B * ∑ n ∈ K, ‖a n‖^2 := by
  let v : ι → EuclideanSpace ℂ K := fun i => WithLp.toLp 2 (fun n => conj (A i n))
  let u : EuclideanSpace ℂ K := WithLp.toLp 2 (fun n => a n)
  have hinner (i j : ι) : inner ℂ (v i) (v j) = ∑ n ∈ K, A i n * conj (A j n) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply']
    change (∑ n : K, conj (conj (A i n)) * conj (A j n)) = _
    simp only [conj_conj]
    exact sum_coe_sort K (fun n => A i n * conj (A j n))
  have heval (i : ι) : inner ℂ (v i) u = ∑ n ∈ K, A i n * a n := by
    simp only [PiLp.inner_apply, RCLike.inner_apply']
    change (∑ n : K, conj (conj (A i n)) * a n) = _
    simp only [conj_conj]
    exact sum_coe_sort K (fun n => A i n * a n)
  have hnorm : ‖u‖^2 = ∑ n ∈ K, ‖a n‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ n : K, ‖a n‖^2) = _
    exact sum_coe_sort K (fun n => ‖a n‖^2)
  have hr : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B := by
    simpa only [hinner] using hrow
  simpa only [heval, hnorm] using mrt_gram_analysis S v u hB hr

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparsePolynomial
namespace OAI

/-! The sparse Gram bound for the actual finite exponential polynomial.
The optional nonnegative weight permits a smooth integer majorant. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.ComplexConjugate


theorem mrt_sparse_weighted_polynomial_energy {ι : Type*} (K : Finset ι)
    (w freq : ι → ℝ) (a : ι → ℂ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (S : Finset ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ t ∈ S, ∑ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤ B) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)*a n) freq t‖^2) ≤
      B * ∑ n ∈ K, w n*‖a n‖^2 := by
  let A := fun t n => (Real.sqrt (w n):ℂ)*Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I)
  let b := fun n => (Real.sqrt (w n):ℂ)*a n
  have hs (n : ι) (hn : n ∈ K) : (Real.sqrt (w n):ℂ)*(Real.sqrt (w n):ℂ) = w n := by
    exact_mod_cast Real.mul_self_sqrt (hw n hn)
  have hp (t s : ℝ) : (∑ n ∈ K, A t n * conj (A s n)) =
      mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s) := by
    apply sum_congr rfl
    intro n hn
    dsimp only [A, mrtExponentialPolynomial]
    rw [map_mul, conj_ofReal]
    calc
      _ = ((Real.sqrt (w n):ℂ)*(Real.sqrt (w n):ℂ)) *
          (Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I) *
            conj (Complex.exp (((freq n*s:ℝ):ℂ)*Complex.I))) := by ring
      _ = _ := by
        rw [hs n hn, mrt_phase_pair]
        rw [show freq n*t-freq n*s = freq n*(t-s) by ring]
  have he (t : ℝ) : (∑ n ∈ K, A t n*b n) =
      mrtExponentialPolynomial K (fun n => (w n:ℂ)*a n) freq t := by
    apply sum_congr rfl
    intro n hn
    dsimp only [A, b, mrtExponentialPolynomial]
    calc
      _ = ((Real.sqrt (w n):ℂ)*(Real.sqrt (w n):ℂ))*a n*
          Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I) := by ring
      _ = _ := by rw [hs n hn]
  have hm : (∑ n ∈ K, ‖b n‖^2) = ∑ n ∈ K, w n*‖a n‖^2 := by
    apply sum_congr rfl
    intro n hn
    simp only [b, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hw n hn)]
  have hr : ∀ t ∈ S, ∑ s ∈ S, ‖∑ n ∈ K, A t n*conj (A s n)‖ ≤ B := by
    simpa only [hp] using hrow
  simpa only [he, hm] using mrt_finite_matrix_gram S K A b hB hr

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseRows
namespace OAI

/-! Summable Gram rows on one-separated heights.  A square-root frequency
remainder costs only the number of sampled heights, not the full interval. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_separated_cauchy_sum {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |x i-x j|) :
    (∑ i ∈ S, 1/(1+(x i)^2)) ≤ 8 := by
  let b := fun i => ⌊|x i|⌋₊
  let L := S.sup b
  let F := fun j => S.filter (fun i => b i = j)
  have hindex (i : ι) (hi : i ∈ S) : b i ≤ L := le_sup hi
  have hband (j : ℕ) (i : ι) (hi : i ∈ F j) :
      (j:ℝ) ≤ |x i| ∧ |x i| < (j:ℝ)+1 := by
    have he := (mem_filter.mp hi).2
    have hl := Nat.floor_le (abs_nonneg (x i))
    have hu := Nat.lt_floor_add_one |x i|
    change (b i:ℝ) ≤ |x i| at hl
    change |x i| < (b i:ℝ)+1 at hu
    rw [he] at hl hu
    exact ⟨hl,hu⟩
  have hcard (j : ℕ) : (F j).card ≤ 2 := by
    apply (card_le_card (s := F j) (t := S.filter
      (fun i => (j:ℝ) ≤ |x i| ∧ |x i| < (j:ℝ)+1)) ?_).trans
      (minor_arc_absolute_band_packing S x 1 j hsep)
    intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).1, hband j i hi⟩
  have hpiece (j : ℕ) : (∑ i ∈ F j, 1/(1+(x i)^2)) ≤ 2/(1+(j:ℝ)^2) := by
    calc
      _ ≤ ∑ _i ∈ F j, 1/(1+(j:ℝ)^2) := by
        apply sum_le_sum
        intro i hi
        have hs := pow_le_pow_left₀ (Nat.cast_nonneg j) (hband j i hi).1 2
        rw [sq_abs] at hs
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = ((F j).card:ℝ)/(1+(j:ℝ)^2) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard j) (by positivity)
  have hpartition : (∑ i ∈ S, 1/(1+(x i)^2)) =
      ∑ j ∈ Icc 0 L, ∑ i ∈ F j, 1/(1+(x i)^2) := by
    symm
    exact sum_fiberwise_of_maps_to
      (fun i hi => mem_Icc.mpr ⟨Nat.zero_le _, hindex i hi⟩) _
  have hI : Icc 0 L = insert 0 (Ioc 0 L) := by
    ext j
    simp only [mem_Icc, mem_insert, mem_Ioc]
    omega
  have htail := mrt_quadratic_gap_sum (by norm_num : (0:ℝ)<1) L
  simp only [div_one] at htail
  rw [hpartition]
  apply (sum_le_sum (fun j _ => hpiece j)).trans
  rw [hI, sum_insert (by simp)]
  simp only [Nat.cast_zero, zero_pow (by omega : 2≠0), add_zero, div_one]
  have he : (∑ j ∈ Ioc 0 L, 2/(1+(j:ℝ)^2)) =
      2 * ∑ j ∈ Ioc 0 L, (1+(j:ℝ)^2)⁻¹ := by
    simp only [div_eq_mul_inv, mul_sum]
  rw [he]
  linarith

theorem mrt_sparse_weighted_row_energy {ι : Type*} (K : Finset ι)
    (w freq : ι → ℝ) (a : ι → ℂ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (S : Finset ℝ) (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤
        A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)*a n) freq t‖^2) ≤
      (8*A+(S.card:ℝ)*D) * ∑ n ∈ K, w n*‖a n‖^2 := by
  apply mrt_sparse_weighted_polynomial_energy K w freq a hw S (by positivity)
  intro t ht
  have hc : (∑ s ∈ S, 1/(1+(t-s)^2)) ≤ 8 := by
    apply mrt_separated_cauchy_sum S (fun s => t-s)
    intro s hs u hu hsu
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hsep s hs u hu hsu
  calc
    _ ≤ ∑ s ∈ S, (A/(1+(t-s)^2)+D) := sum_le_sum (fun s hs => hkernel t ht s hs)
    _ = A*(∑ s ∈ S, 1/(1+(t-s)^2))+(S.card:ℝ)*D := by
      simp only [sum_add_distrib, div_eq_mul_inv, mul_sum, sum_const, nsmul_eq_mul,
        one_mul]
    _ ≤ A*8+(S.card:ℝ)*D := add_le_add (mul_le_mul_of_nonneg_left hc hA) le_rfl
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseMajorant
namespace OAI

/-! Removing the artificial smooth coefficient weight on the original
finite polynomial support. The majorant need only be at least one there. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical

theorem mrt_sparse_majorized_energy {ι : Type*} (K P : Finset ι) (hPK : P ⊆ K)
    (w freq : ι → ℝ) (a : ι → ℂ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (hwP : ∀ n ∈ P, 1 ≤ w n) (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤
        A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a freq t‖^2) ≤
      (8*A+(S.card:ℝ)*D) * ∑ n ∈ P, ‖a n‖^2 := by
  let b := fun n => if n ∈ P then a n/(w n:ℂ) else 0
  have hb (n : ι) (hn : n ∈ P) : (w n:ℂ)*b n = a n := by
    have hpos : 0 < w n := lt_of_lt_of_le zero_lt_one (hwP n hn)
    have hnz : (w n:ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    dsimp only [b]
    rw [if_pos hn]
    field_simp
  have he (t : ℝ) : mrtExponentialPolynomial K (fun n => (w n:ℂ)*b n) freq t =
      mrtExponentialPolynomial P a freq t := by
    unfold mrtExponentialPolynomial
    calc
      _ = ∑ n ∈ P, (w n:ℂ)*b n*Complex.exp (((freq n*t:ℝ):ℂ)*I) := by
        symm
        apply sum_subset hPK
        intro n _ hn
        simp [b,hn]
      _ = _ := sum_congr rfl (fun n hn => by rw [hb n hn])
  have hmass : (∑ n ∈ K, w n*‖b n‖^2) ≤ ∑ n ∈ P, ‖a n‖^2 := by
    calc
      _ = ∑ n ∈ P, w n*‖b n‖^2 := by
        symm
        apply sum_subset hPK
        intro n _ hn
        simp [b,hn]
      _ ≤ _ := by
        apply sum_le_sum
        intro n hn
        have hpos : 0 < w n := lt_of_lt_of_le zero_lt_one (hwP n hn)
        dsimp only [b]
        rw [if_pos hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hpos]
        calc
          _ = ‖a n‖^2/w n := by field_simp
          _ ≤ _ := div_le_self (sq_nonneg _) (hwP n hn)
  have h := mrt_sparse_weighted_row_energy K w freq b hw S hsep hA hD hkernel
  simp_rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hmass (by positivity))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralTypical
namespace OAI

/-! The actual typical-set Ramaré approximation for ordinary
multiplicative functions. Prime squares account for every failure of
complete multiplicativity, before any frequency-class witness cover. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrtCofactorPolynomial_continuous (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a : ℝ) : Continuous (mrtCofactorPolynomial P F N a) := by
  unfold mrtCofactorPolynomial
  apply continuous_finsetSum
  intro m _
  by_cases hw : (N : ℝ) < a * m ∧ a * m ≤ 2 * N
  · simp only [if_pos hw]
    unfold mrtDirichletAtom
    fun_prop
  · simp only [if_neg hw]
    exact continuous_const



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function



variable {𝕂 : Type*} [RCLike 𝕂]








@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

















local notation (name := mellintransform) "𝓜" => mellin















@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le


























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseCells
namespace OAI

/-! Unit cells for the elementary power-sum approximation. Centering the
cells cancels the linear phase error, leaving a summable quadratic error. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset


@[simp] lemma halasz_power_phase_norm (t x : ℝ) : ‖halaszPowerPhase t x‖ = 1 := by
  simp [halaszPowerPhase, Complex.norm_exp, Complex.mul_re]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleWeight
namespace OAI

/-! A continuous compactly supported majorant of a dyadic interval.
The adjoining affine pieces have exactly the integrals already estimated. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory


lemma halasz_triangle_weight_nonneg (N x : ℝ) : 0 ≤ halaszTriangleWeight N x :=
  le_max_left _ _






lemma halasz_triangle_weight_dyadic (N x : ℝ) (hN : 0 < N)
    (hx : x ∈ Set.Icc N (2*N)) : 1 ≤ halaszTriangleWeight N x := by
  unfold halaszTriangleWeight
  apply le_max_of_le_right
  apply le_min
  · have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
    nlinarith [hx.1]
  · have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
    nlinarith [hx.2]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPoissonBound
namespace OAI

/-! Summing the stationary and nonstationary Poisson modes. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma halasz_integer_square_mass_nonneg : 0 ≤ halaszIntegerSquareMass :=
  tsum_nonneg (fun _ => by positivity)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCofactorWindow
namespace OAI

/-! The cofactor polynomial has an actual fixed multiplicative window.
Finite partial summation turns its ordinary reciprocal-count prefix bound
into a pointwise bound for that polynomial. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

lemma mrt_cofactor_window_set (N : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    ((Icc 1 (4 * N)).filter (fun m : ℕ => (N : ℝ) < a * (m : ℝ) ∧ a * (m : ℝ) ≤ 2 * N)) =
      Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊ := by
  have ha0 : 0 < a := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hfloor : ⌊(2 * N : ℝ) / a⌋₊ ≤ 4 * N := by
    apply Nat.floor_le_of_le
    have hdiv : (2 * N : ℝ) / a ≤ 2 * N := div_le_self (by positivity) ha
    push_cast
    linarith
  ext m
  constructor
  · intro hm
    obtain ⟨hm, hlo, hhi⟩ := mem_filter.mp hm
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (div_nonneg hN0 ha0.le)).mpr
      apply (div_lt_iff₀ ha0).mpr
      simpa only [mul_comm] using hlo
    · apply Nat.le_floor
      apply (le_div_iff₀ ha0).mpr
      simpa only [mul_comm] using hhi
  · intro hm
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hm
    have hloR := (Nat.floor_lt (div_nonneg hN0 ha0.le)).mp hlo
    have hhiR : (m : ℝ) ≤ (2 * N : ℝ) / a :=
      (Nat.le_floor_iff (by positivity)).mp hhi
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, hhi.trans hfloor⟩, ?_⟩
    constructor
    · simpa only [mul_comm] using (div_lt_iff₀ ha0).mp hloR
    · simpa only [mul_comm] using (le_div_iff₀ ha0).mp hhiR

lemma mrt_cofactor_window_ratio (N : ℕ) {a : ℝ} (ha : 0 < a)
    (hx : 2 ≤ (N : ℝ) / a) :
    0 < ⌊(N : ℝ) / a⌋₊ ∧
      ⌊(N : ℝ) / a⌋₊ ≤ ⌊(2 * N : ℝ) / a⌋₊ ∧
      ⌊(2 * N : ℝ) / a⌋₊ ≤ 3 * ⌊(N : ℝ) / a⌋₊ := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm2 : 2 ≤ ⌊(N : ℝ) / a⌋₊ := Nat.le_floor (by exact hx)
  have hlow := Nat.lt_floor_add_one ((N : ℝ) / a)
  have hhigh := Nat.floor_le (show 0 ≤ (2 * N : ℝ) / a by positivity)
  have hdouble : (N : ℝ) / a ≤ (2 * N : ℝ) / a := by
    calc
      _ ≤ 2 * ((N : ℝ) / a) := by linarith
      _ = _ := by ring
  refine ⟨by omega, Nat.floor_le_floor hdouble, ?_⟩
  have hid : (2 * N : ℝ) / a = 2 * ((N : ℝ) / a) := by ring
  conv at hhigh => rhs; rw [hid]
  have hm2R : (2 : ℝ) ≤ ⌊(N : ℝ) / a⌋₊ := by exact_mod_cast hm2
  have hu : (⌊(2 * N : ℝ) / a⌋₊ : ℝ) ≤ 3 * (⌊(N : ℝ) / a⌋₊ : ℝ) := by linarith
  exact_mod_cast hu




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCofactorMean
namespace OAI

/-! A mean-square bound for the actual fixed-window cofactor polynomial.
The reciprocal-count weight is a contraction, so this estimate is uniform
in all remaining typical-factorization masks. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_cofactor_exponential_polynomial (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    mrtCofactorPolynomial P F N a t =
      mrtExponentialPolynomial (Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtCofactorPolynomial
  rw [← sum_filter, mrt_cofactor_window_set N ha]
  unfold mrtExponentialPolynomial
  apply sum_congr rfl
  intro n _
  unfold mrtDirichletAtom
  ring

lemma mrt_reciprocal_count_oneBounded (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) :
    OneBounded (fun n => F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) := by
  intro n hn
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_one (by positivity : (0 : ℝ) < (finitePrimeDivisorCount P n + 1 : ℕ))).mpr
  exact (hF n hn).trans (by norm_num)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseCofactor
namespace OAI

/-! Sparse mean square with the actual reciprocal prime-count cofactor.
All coefficient and rounding normalizations are proved here. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical

lemma mrt_cofactor_coefficient_square_mass (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) :
    (∑ k ∈ Ioc ⌊(N:ℝ)/a⌋₊ ⌊(2*N:ℝ)/a⌋₊,
      ‖(F k/((finitePrimeDivisorCount P k+1:ℕ):ℂ))/(k:ℂ)‖^2) ≤ 2*a/N := by
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hN : (0:ℝ) < N := by
    have hh := (le_div_iff₀ ha0).mp hx
    linarith
  obtain ⟨hm,hmn,_⟩ := mrt_cofactor_window_ratio N ha0 hx
  change 0 < m at hm
  change m ≤ n at hmn
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hlower : (N:ℝ)/a ≤ 2*m := by
    have hfloor := Nat.lt_floor_add_one ((N:ℝ)/a)
    change (N:ℝ)/a < (m:ℝ)+1 at hfloor
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hcoeff := mrt_reciprocal_count_oneBounded P F hF
  change (∑ k ∈ Ioc m n, _) ≤ _
  calc
    _ ≤ ∑ k ∈ Ioc m n, ((k:ℝ)^2)⁻¹ := by
      apply sum_le_sum
      intro k hk
      have hk0 := hm.trans (mem_Ioc.mp hk).1
      have hkR : (0:ℝ) < k := by exact_mod_cast hk0
      rw [norm_div, Complex.norm_natCast]
      calc
        _ ≤ (1/(k:ℝ))^2 := pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_right (hcoeff k hk0) hkR.le) 2
        _ = _ := by simp
    _ ≤ (m:ℝ)⁻¹-(n:ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hm.ne' hmn
    _ ≤ (m:ℝ)⁻¹ := sub_le_self _ (by positivity)
    _ ≤ 2*a/N := by
      rw [inv_eq_one_div, div_le_iff₀ hm0]
      have hh := (div_le_iff₀ ha0).mp hlower
      calc
        (1:ℝ) = (N:ℝ)/N := by field_simp
        _ ≤ (2*a*m)/N := div_le_div_of_nonneg_right (by nlinarith) hN.le
        _ = _ := by ring

theorem mrt_sparse_cofactor_energy (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (hx : 2 ≤ (N:ℝ)/a)
    (K : Finset ℕ) (hK : Ioc ⌊(N:ℝ)/a⌋₊ ⌊(2*N:ℝ)/a⌋₊ ⊆ K)
    (w : ℕ → ℝ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (hw1 : ∀ n ∈ Ioc ⌊(N:ℝ)/a⌋₊ ⌊(2*N:ℝ)/a⌋₊, 1 ≤ w n)
    (S : Finset ℝ) (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ))
        (fun n => -Real.log (n:ℝ)) (t-s)‖ ≤ A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtCofactorPolynomial P F N a t‖^2) ≤
      (8*A+(S.card:ℝ)*D)*(2*a/N) := by
  simp_rw [mrt_cofactor_exponential_polynomial P F N ha]
  apply (mrt_sparse_majorized_energy K _ hK w (fun n => -Real.log (n:ℝ))
    (fun n => (F n/((finitePrimeDivisorCount P n+1:ℕ):ℂ))/(n:ℂ))
    hw hw1 S hsep hA hD hkernel).trans
  exact mul_le_mul_of_nonneg_left
    (mrt_cofactor_coefficient_square_mass P F hF N ha hx) (by positivity)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSparseCofactor
namespace OAI

/-! The proved integer kernel attached to actual reciprocal-count cofactors. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_triangle_dyadic_member (M : ℝ) (hM : 0 < M) (n : ℕ)
    (hn : n ∈ Ioc ⌊M⌋₊ ⌊2*M⌋₊) :
    n ∈ halaszTriangleSupport M ∧ 1 ≤ halaszTriangleWeight M n := by
  have hlow : M < n := (Nat.floor_lt hM.le).mp (mem_Ioc.mp hn).1
  have hu : (n:ℝ) ≤ 2*M :=
    (Nat.cast_le.mpr (mem_Ioc.mp hn).2).trans (Nat.floor_le (by positivity))
  refine ⟨?_,halasz_triangle_weight_dyadic M n hM ⟨hlow.le,hu⟩⟩
  apply mem_range.mpr
  change n < ⌈5*M/2⌉₊+1
  apply Nat.lt_succ_of_le
  exact_mod_cast (show (n:ℝ) ≤ (⌈5*M/2⌉₊:ℝ) from
    (hu.trans (by linarith)).trans (Nat.le_ceil (5*M/2)))


/-- An unconditional sparse mean square for the literal cofactor window. -/
theorem halasz_sparse_cofactor_energy (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) {T : ℝ} (hT : 0 ≤ T)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) :
    (∑ t ∈ S, ‖mrtCofactorPolynomial P F N a t‖^2) ≤
      (148800*((N:ℝ)/a)+(S.card:ℝ)*halaszSparseKernelError ((N:ℝ)/a) T)*(2*a/N) := by
  have hM : 0 < (N:ℝ)/a := lt_of_lt_of_le (by norm_num) hx
  have he : (2*N:ℝ)/a = 2*((N:ℝ)/a) := by ring
  have hmem (n : ℕ) (hn : n ∈ Ioc ⌊(N:ℝ)/a⌋₊ ⌊(2*N:ℝ)/a⌋₊) :=
    halasz_triangle_dyadic_member ((N:ℝ)/a) hM n (by rwa [he] at hn)
  have h := mrt_sparse_cofactor_energy P F hF N ha hx
    (halaszTriangleSupport ((N:ℝ)/a)) (fun n hn => (hmem n hn).1)
    (fun n => halaszTriangleWeight ((N:ℝ)/a) n) (fun n _ => halasz_triangle_weight_nonneg _ n)
    (fun n hn => (hmem n hn).2) S hsep
    (by positivity : 0 ≤ 18600*((N:ℝ)/a))
    (by
      dsimp [halaszSparseKernelError]
      exact add_nonneg (by positivity) (mul_nonneg (by positivity) halasz_integer_square_mass_nonneg))
    (halasz_integer_kernel_on_samples ((N:ℝ)/a) T hM hT S hS)
  convert (preTransparency := .instances) h using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyCover
namespace OAI

/-! Refinement of a later frequency class by its actual preceding-bin
large-value witnesses. The witnesses may overlap; the finite sum charges
each preceding bin explicitly. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_nonnegative_integral_cover {ι : Type*} (I : Finset ι)
    (E : ι → Set ℝ) (hE : ∀ i ∈ I, MeasurableSet (E i)) {S : Set ℝ}
    (hS : MeasurableSet S) (f : ℝ → ℝ) (hf : IntegrableOn f S)
    (hf0 : ∀ t ∈ S, 0 ≤ f t) (hcover : ∀ t ∈ S, ∃ i ∈ I, t ∈ E i) :
    (∫ t in S, f t) ≤ ∑ i ∈ I, ∫ t in S ∩ E i, f t := by
  have hi (i : ι) (hmem : i ∈ I) : IntegrableOn ((E i).indicator f) S :=
    hf.indicator (hE i hmem)
  calc
    _ ≤ ∫ t in S, ∑ i ∈ I, (E i).indicator f t := by
      apply setIntegral_mono_on hf (integrable_finsetSum I hi) hS
      intro t ht
      obtain ⟨i, hiI, hit⟩ := hcover t ht
      calc
        f t = (E i).indicator f t := (Set.indicator_of_mem hit f).symm
        _ ≤ ∑ i ∈ I, (E i).indicator f t := by
          apply single_le_sum _ hiI
          intro k _
          by_cases hk : t ∈ E k
          · rw [Set.indicator_of_mem hk f]
            exact hf0 t ht
          · rw [Set.indicator_of_notMem hk f]
    _ = ∑ i ∈ I, ∫ t in S, (E i).indicator f t := integral_finsetSum I hi
    _ = _ := by
      apply sum_congr rfl
      intro i hiI
      exact setIntegral_indicator (hE i hiI)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSetSampling
namespace OAI

/-! A bounded measurable frequency set can be sampled in two separated
classes. Sample points stay in the original set, so its large-value witnesses
are preserved without taking a neighbourhood or differentiating them. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_unit_cell_sample (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ t, 0 ≤ G t) {E : Set ℝ} (hE : MeasurableSet E)
    (a : ℝ) (hsub : E ⊆ Set.Ioc a (a+1)) (hne : E.Nonempty) :
    ∃ t ∈ E, (∫ u in E, G u) ≤ 2*G t := by
  have hab : a ≤ a+1 := by linarith
  have hiI : IntegrableOn G (Set.Ioc a (a+1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    (hG.intervalIntegrable a (a+1))
  have hi := hiI.mono_set hsub
  by_contra hn
  push Not at hn
  let C := ∫ u in E, G u
  have hC : 0 < C := by
    obtain ⟨t,ht⟩ := hne
    have hh := hn t ht
    dsimp only [C]
    linarith [hG0 t]
  have hiConst : IntegrableOn (fun _ : ℝ => C/2) (Set.Ioc a (a+1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    ((continuous_const : Continuous (fun _ : ℝ => C/2)).intervalIntegrable a (a+1))
  have hc : C ≤ C/2 := by
    calc
      _ ≤ ∫ u in E, C/2 := setIntegral_mono_on hi (hiConst.mono_set hsub) hE
        (fun t ht => by have hh := hn t ht; change 2*G t < C at hh; linarith)
      _ ≤ ∫ u in Set.Ioc a (a+1), C/2 := setIntegral_mono_set hiConst
        (Filter.Eventually.of_forall (fun _ => by change 0 ≤ C/2; positivity))
        (Filter.Eventually.of_forall hsub)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const]
        simp
  linarith

lemma mrt_cell_sample_injective (J : Finset ℕ) (a : ℝ) (x : ℕ → ℝ)
    (hx : ∀ k ∈ J, x k ∈ Set.Ioc (a+k) (a+k+1)) :
    Set.InjOn x J := by
  intro k hk l hl hkl
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hn : (k:ℝ)+1 ≤ l := by exact_mod_cast hlt
    have h1 := hx k hk
    have h2 := hx l hl
    rw [hkl] at h1
    linarith [h1.2,h2.1]
  · have hn : (l:ℝ)+1 ≤ k := by exact_mod_cast hlt
    have h1 := hx k hk
    have h2 := hx l hl
    rw [hkl] at h1
    linarith [h1.1,h2.2]

lemma mrt_cell_sample_separated (J : Finset ℕ) (a : ℝ) (x : ℕ → ℝ)
    (hx : ∀ k ∈ J, x k ∈ Set.Ioc (a+k) (a+k+1))
    (hpar : ∀ k ∈ J, ∀ l ∈ J, k%2 = l%2) :
    ∀ t ∈ J.image x, ∀ s ∈ J.image x, t≠s → 1 ≤ |t-s| := by
  intro t ht s hs hts
  obtain ⟨k,hk,rfl⟩ := mem_image.mp ht
  obtain ⟨l,hl,rfl⟩ := mem_image.mp hs
  have hne : k≠l := fun h => hts (congrArg x h)
  have hmod := hpar k hk l hl
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hnat : k+2 ≤ l := by omega
    have hcast : (k:ℝ)+2 ≤ l := by exact_mod_cast hnat
    have h1 := hx k hk
    have h2 := hx l hl
    rw [abs_of_nonpos (by linarith [h1.2,h2.1] : x k-x l ≤ 0)]
    linarith [h1.2,h2.1]
  · have hnat : l+2 ≤ k := by omega
    have hcast : (l:ℝ)+2 ≤ k := by exact_mod_cast hnat
    have h1 := hx k hk
    have h2 := hx l hl
    rw [abs_of_nonneg (by linarith [h1.1,h2.2] : 0 ≤ x k-x l)]
    linarith [h1.1,h2.2]

/-- A uniform bound on all separated samples gives a bound on the actual
set integral, with the sample points still lying in that set. -/
theorem mrt_set_integral_of_samples (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ t, 0 ≤ G t) {E : Set ℝ} (hE : MeasurableSet E)
    {T B : ℝ} (hT : 0 ≤ T) (hET : E ⊆ Set.Ioc (-T) T)
    (hsamples : ∀ S : Finset ℝ, (∀ t ∈ S, t ∈ E) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) → ∑ t ∈ S, G t ≤ B) :
    (∫ t in E, G t) ≤ 4*B := by
  let N := ⌈2*T⌉₊
  let cell := fun k : ℕ => Set.Ioc (-T+k) (-T+k+1)
  let J := (range N).filter (fun k => (E ∩ cell k).Nonempty)
  have hselect (k : ℕ) (hk : k ∈ J) :
      ∃ t ∈ E ∩ cell k, (∫ u in E ∩ cell k, G u) ≤ 2*G t :=
    mrt_unit_cell_sample G hG hG0 (hE.inter measurableSet_Ioc) (-T+k)
      Set.inter_subset_right (mem_filter.mp hk).2
  let x := fun k => if hk : k ∈ J then Classical.choose (hselect k hk) else 0
  have hx (k : ℕ) (hk : k ∈ J) : x k ∈ E ∩ cell k ∧
      (∫ u in E ∩ cell k, G u) ≤ 2*G (x k) := by
    simpa only [x, dif_pos hk] using Classical.choose_spec (hselect k hk)
  have hcover (t : ℝ) (ht : t ∈ E) : ∃ k ∈ range N, t ∈ cell k := by
    have ht' := hET ht
    have hpos : 0 < t+T := by linarith [ht'.1]
    have hcpos : 0 < ⌈t+T⌉₊ := Nat.ceil_pos.mpr hpos
    have hcN : ⌈t+T⌉₊ ≤ N := Nat.ceil_mono (by linarith [ht'.2])
    let k := ⌈t+T⌉₊-1
    have hsucc : k+1 = ⌈t+T⌉₊ := by dsimp [k]; omega
    have hcast : (k:ℝ)+1 = (⌈t+T⌉₊:ℝ) := by exact_mod_cast hsucc
    refine ⟨k,mem_range.mpr (by omega),?_⟩
    have hlo := Nat.ceil_lt_add_one hpos.le
    have hhi := Nat.le_ceil (t+T)
    change -T+(k:ℝ) < t ∧ t ≤ -T+(k:ℝ)+1
    constructor <;> linarith
  have hi : IntegrableOn G (Set.Ioc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -T ≤ T)).mp
    (hG.intervalIntegrable (-T) T)
  have hc := mrt_nonnegative_integral_cover (range N) cell
    (fun _ _ => measurableSet_Ioc) hE G (hi.mono_set hET)
    (fun t _ => hG0 t) hcover
  have he : (∑ k ∈ range N, ∫ t in E ∩ cell k, G t) =
      ∑ k ∈ J, ∫ t in E ∩ cell k, G t := by
    symm
    apply sum_subset (filter_subset _ _)
    intro k hk hkJ
    have hn : ¬(E ∩ cell k).Nonempty := fun h => hkJ (mem_filter.mpr ⟨hk,h⟩)
    rw [Set.not_nonempty_iff_eq_empty.mp hn]
    simp
  rw [he] at hc
  have hp (I : Finset ℕ) (hIJ : I ⊆ J)
      (hpar : ∀ k ∈ I, ∀ l ∈ I, k%2=l%2) : (∑ k ∈ I, G (x k)) ≤ B := by
    have hcell (k : ℕ) (hk : k ∈ I) : x k ∈ cell k := (hx k (hIJ hk)).1.2
    have hbound := hsamples (I.image x)
      (fun t ht => by obtain ⟨k,hk,rfl⟩ := mem_image.mp ht; exact (hx k (hIJ hk)).1.1)
      (mrt_cell_sample_separated I (-T) x hcell hpar)
    rw [sum_image (mrt_cell_sample_injective I (-T) x hcell)] at hbound
    exact hbound
  have h0 := hp (J.filter (fun k => k%2=0)) (filter_subset _ _)
    (fun k hk l hl => (mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm)
  have h1 := hp (J.filter (fun k => ¬k%2=0)) (filter_subset _ _)
    (fun k hk l hl => by have hkm := (mem_filter.mp hk).2; have hlm := (mem_filter.mp hl).2; omega)
  have hs : (∑ k ∈ J, G (x k)) ≤ 2*B := by
    have he := sum_filter_add_sum_filter_not J (fun k => k%2=0) (fun k => G (x k))
    linarith
  calc
    _ ≤ ∑ k ∈ J, ∫ t in E ∩ cell k, G t := hc
    _ ≤ ∑ k ∈ J, 2*G (x k) := sum_le_sum (fun k hk => (hx k hk).2)
    _ = 2*∑ k ∈ J, G (x k) := (mul_sum _ _ _).symm
    _ ≤ 4*B := by linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmallPrimeSamples
namespace OAI

/-! The small additional-prime branch, using the proved integer kernel. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_sparse_cofactor_bounded (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) {T : ℝ} (hT : 0 ≤ T)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    (hcost : (S.card:ℝ)*halaszSparseKernelError ((N:ℝ)/a) T ≤ (N:ℝ)/a) :
    (∑ t ∈ S, ‖mrtCofactorPolynomial P F N a t‖^2) ≤ 297602 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hN : (0:ℝ) < N := by
    have hh := (le_div_iff₀ ha0).mp hx
    linarith
  apply (halasz_sparse_cofactor_energy P F hF N ha hx hT S hS hsep).trans
  calc
    _ ≤ (148800*((N:ℝ)/a)+(N:ℝ)/a)*(2*a/N) :=
      mul_le_mul_of_nonneg_right (add_le_add_right hcost _) (by positivity)
    _ = 297602 := by field_simp; ring



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraSmallIntegral
namespace OAI

/-! Small additional-prime values on the actual no-small class. The
integer-kernel error is paid by the final original-band sample count. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_small_cofactor_integral_oai (A : Finset ℕ) (B : ℕ → ℂ)
    (hB : OneBounded B) (N : ℕ) {a T θ : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) (hT : 0 ≤ T) (Q : ℝ → ℂ) (hQ : Continuous Q)
    {E : Set ℝ} (hE : MeasurableSet E) (hET : E ⊆ Set.Ioc (-T) T)
    (hcost : ∀ S : Finset ℝ, (∀ t ∈ S, t ∈ E) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (S.card:ℝ)*halaszSparseKernelError ((N:ℝ)/a) T ≤ (N:ℝ)/a)
    (hsmall : ∀ t ∈ E, ‖Q t‖ ≤ θ) :
    (∫ t in E, ‖Q t*mrtCofactorPolynomial A B N a t‖^2) ≤ 1190408*θ^2 := by
  have hh := mrt_set_integral_of_samples
    (fun t => ‖Q t*mrtCofactorPolynomial A B N a t‖^2)
    ((hQ.mul (mrtCofactorPolynomial_continuous A B N a)).norm.pow 2)
    (fun _ => sq_nonneg _) hE hT hET (B := 297602*θ^2) (by
      intro S hS hsep
      have hfreq : ∀ t ∈ S, |t| ≤ T := by
        intro t ht
        obtain ⟨hl,hu⟩ := hET (hS t ht)
        exact abs_le.mpr ⟨by linarith,hu⟩
      have he := halasz_sparse_cofactor_bounded A B hB N ha hx hT S hfreq hsep
        (hcost S hS hsep)
      calc
        _ ≤ ∑ t ∈ S, θ^2*‖mrtCofactorPolynomial A B N a t‖^2 := by
          apply sum_le_sum
          intro t ht
          rw [norm_mul,mul_pow]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hsmall t (hS t ht)) 2) (sq_nonneg _)
        _ = θ^2*∑ t ∈ S, ‖mrtCofactorPolynomial A B N a t‖^2 := (mul_sum _ _ _).symm
        _ ≤ θ^2*297602 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
        _ = _ := by ring)
  linarith


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_small_cofactor_integral_oai := @OAI.TwoPointCorrelations.mrt_small_cofactor_integral_oai
