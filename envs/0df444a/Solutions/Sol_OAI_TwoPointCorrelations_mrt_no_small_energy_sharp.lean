-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_no_small_energy_sharp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:56:41.365952+00:00
-- url     : https://prove2.me/submissions/ad7faaaa-e16d-4ba5-9d24-9880c6fa7cdd

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_extra_prime_avoidance
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_extra_prime_mean_square
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_no_small_coarse_energy

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MertensScale
namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The formal proof uses the bounded-error statement
`RS_prime.mertens_second_theorem'`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma sievePrimesUpTo_prime (y : ℝ) (p : ℕ) (hp : p ∈ sievePrimesUpTo y) :
    Nat.Prime p := (mem_filter.mp hp).2

lemma sievePrimesUpTo_le (y : ℝ) (hy : 0 ≤ y) (p : ℕ)
    (hp : p ∈ sievePrimesUpTo y) : (p : ℝ) ≤ y := by
  exact (Nat.le_floor_iff hy).mp (mem_Iic.mp (mem_filter.mp hp).1)



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquareKernel
namespace OAI

/-!
# Exponential majorant for Dirichlet-polynomial mean squares

This is the elementary kernel behind the mean-value estimate used at the
start of corrected MRT, Appendix A, Proposition A.3.  Its Fourier transform
has quadratic decay, so the ensuing row sum loses no logarithm.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Set


lemma mrtMeanSquareKernel_right {T : ℝ} (ω : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonneg ht,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_left {T : ℝ} (ω : ℝ) {t : ℝ} (ht : t ≤ 0) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonpos ht, neg_neg,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_integrable {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    Integrable (mrtMeanSquareKernel T ω) := by
  have hr : IntegrableOn (mrtMeanSquareKernel T ω) (Ioi 0) := by
    apply (integrableOn_exp_mul_complex_Ioi
      (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0).congr_fun
        (fun t ht => ?_) measurableSet_Ioi
    simpa using (mrtMeanSquareKernel_right ω ht.le).symm
  have hl : IntegrableOn (mrtMeanSquareKernel T ω) (Iic 0) := by
    apply (integrableOn_exp_mul_complex_Iic
      (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using one_div_pos.mpr hT) 0).congr_fun
        (fun t ht => ?_) measurableSet_Iic
    exact (mrtMeanSquareKernel_left ω ht).symm
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

/-- Exact quadratic-decay Fourier transform, without an asymptotic constant. -/
theorem integral_mrtMeanSquareKernel {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    (∫ t : ℝ, mrtMeanSquareKernel T ω t) =
      ((2 * T / (1 + T ^ 2 * ω ^ 2) : ℝ) : ℂ) := by
  have hi := mrtMeanSquareKernel_integrable hT ω
  have hr : (∫ t in Ioi (0 : ℝ), mrtMeanSquareKernel T ω t) =
      -1 / (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), Complex.exp
          ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simpa using mrtMeanSquareKernel_right ω ht.le
      _ = _ := by
        simpa using integral_exp_mul_complex_Ioi
          (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0
  have hl : (∫ t in Iic (0 : ℝ), mrtMeanSquareKernel T ω t) =
      1 / (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Iic (0 : ℝ), Complex.exp
          ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        exact mrtMeanSquareKernel_left ω ht
      _ = _ := by
        simpa using integral_exp_mul_complex_Iic
          (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using one_div_pos.mpr hT) 0
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic, hl, hr]
  have hTp : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hp : (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : (1 / T : ℝ) = 0 := by simpa using this
    exact (one_div_pos.mpr hT).ne' he
  have hm : (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : -(1 / T : ℝ) = 0 := by simpa using this
    exact (neg_lt_zero.mpr (one_div_pos.mpr hT)).ne he
  have hp1 : (1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hm1 : (-1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hd : (1 + T ^ 2 * ω ^ 2 : ℝ) ≠ 0 := by positivity
  have hdc : (1 + (T : ℂ) ^ 2 * (ω : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring_nf
  field_simp [hp1, hm1, hdc]
  ring_nf
  simp only [Complex.I_sq]
  ring

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

lemma mrt_log_gap {x y N : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyN : y ≤ N) :
    (y - x) / N ≤ Real.log y - Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : 0 < N := hy.trans_le hyN
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne', inv_div] at hlog
  calc
    (y - x) / N ≤ (y - x) / y :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hy hyN
    _ = 1 - x / y := by field_simp
    _ ≤ _ := hlog

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

lemma mrt_nat_distance_sum (φ : ℕ → ℝ) (hφ : ∀ k, 0 ≤ φ k)
    {m N : ℕ} (hm : m ∈ Ioc 0 N) :
    (∑ n ∈ Ioc 0 N, φ (Nat.dist n m)) ≤
      φ 0 + 2 * ∑ k ∈ Ioc 0 N, φ k := by
  have hm' := mem_Ioc.mp hm
  have hsplit : Ioc 0 N = Ioc 0 m ∪ Ioc m N := by
    ext n
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 m) (Ioc m N) := by
    rw [disjoint_left]
    simp only [mem_Ioc]
    omega
  have hleft : (∑ n ∈ Ioc 0 m, φ (Nat.dist n m)) = ∑ k ∈ range m, φ k := by
    apply sum_bij (fun n _ => m - n)
    · intro n hn
      have hn' := mem_Ioc.mp hn
      simp only [mem_range]
      omega
    · intro n hn n' hn' he
      have h1 := mem_Ioc.mp hn
      have h2 := mem_Ioc.mp hn'
      omega
    · intro k hk
      have hk' := mem_range.mp hk
      refine ⟨m - k, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rw [Nat.dist_eq_sub_of_le (mem_Ioc.mp hn).2]
  have hright : (∑ n ∈ Ioc m N, φ (Nat.dist n m)) = ∑ k ∈ Ioc 0 (N - m), φ k := by
    apply sum_bij (fun n _ => n - m)
    · intro n hn
      have hn' := mem_Ioc.mp hn
      simp only [mem_Ioc]
      omega
    · intro n hn n' hn' he
      have h1 := mem_Ioc.mp hn
      have h2 := mem_Ioc.mp hn'
      omega
    · intro k hk
      have hk' := mem_Ioc.mp hk
      refine ⟨m + k, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rw [Nat.dist_eq_sub_of_le_right (mem_Ioc.mp hn).1.le]
  have hrange : range m = insert 0 (Ioc 0 (m - 1)) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  have hzero : 0 ∉ Ioc 0 (m - 1) := by simp
  conv_lhs => rw [hsplit, sum_union hd, hleft, hright, hrange, sum_insert hzero]
  have hL : (∑ k ∈ Ioc 0 (m - 1), φ k) ≤ ∑ k ∈ Ioc 0 N, φ k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hk' := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨hk'.1, by omega⟩
    · intro k _ _
      exact hφ k
  have hR : (∑ k ∈ Ioc 0 (N - m), φ k) ≤ ∑ k ∈ Ioc 0 N, φ k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hk' := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨hk'.1, by omega⟩
    · intro k _ _
      exact hφ k
  linarith

lemma mrt_log_nat_gap {m n N : ℕ} (hm : m ∈ Ioc 0 N) (hn : n ∈ Ioc 0 N) :
    (Nat.dist m n : ℝ) / (N : ℝ) ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have hm' := mem_Ioc.mp hm
  have hn' := mem_Ioc.mp hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm'.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
  rcases le_total m n with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm0 (by exact_mod_cast h)))]
    exact mrt_log_gap hm0 (by exact_mod_cast h) (by exact_mod_cast hn'.2)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast h)))]
    exact mrt_log_gap hn0 (by exact_mod_cast h) (by exact_mod_cast hm'.2)

/-- The actual logarithmic-frequency kernel has row sum `O(T+N)`. -/
theorem mrt_logarithmic_kernel_row {T : ℝ} (hT : 0 < T) {N m : ℕ}
    (hm : m ∈ Ioc 0 N) :
    (∑ n ∈ Ioc 0 N,
      2 * T / (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2)) ≤
      8 * (T + (N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (mem_Ioc.mp hm).1.trans_le (mem_Ioc.mp hm).2
  let R := (N : ℝ) / T
  have hR : 0 < R := div_pos hN hT
  have hterm (n : ℕ) (hn : n ∈ Ioc 0 N) :
      2 * T / (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2) ≤
      2 * T * (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ := by
    have hgap := mrt_log_nat_gap hn hm
    rw [abs_sub_comm] at hgap
    have hsq : ((Nat.dist n m : ℝ) / (N : ℝ)) ^ 2 ≤
        (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (by positivity) hgap 2
    have he : ((Nat.dist n m : ℝ) / R) ^ 2 =
        T ^ 2 * ((Nat.dist n m : ℝ) / (N : ℝ)) ^ 2 := by
      dsimp only [R]
      field_simp
    rw [he, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply inv_anti₀ (by positivity)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (sq_nonneg T))
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, 2 * T * (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ :=
      sum_le_sum hterm
    _ = 2 * T * ∑ n ∈ Ioc 0 N, (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ :=
      (mul_sum _ _ _).symm
    _ ≤ 2 * T * (1 + 2 * (2 * R + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hd := mrt_nat_distance_sum (fun k => (1 + ((k : ℝ) / R) ^ 2)⁻¹)
        (fun _ => by positivity) hm
      have hd' : (∑ n ∈ Ioc 0 N, (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹) ≤
          1 + 2 * ∑ k ∈ Ioc 0 N, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by
        simpa only [Nat.cast_zero, zero_div, zero_pow (by decide : 2 ≠ 0), add_zero,
          inv_one] using hd
      exact hd'.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (mrt_quadratic_gap_sum hR N)
          (by norm_num : (0 : ℝ) ≤ 2)))
    _ ≤ 8 * (T + (N : ℝ)) := by
      dsimp only [R]
      have hc : T * ((N : ℝ) / T) = N := mul_div_cancel₀ _ hT.ne'
      nlinarith

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

lemma mrt_weighted_square_expansion {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (T t : ℝ) :
    ((Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S,
        (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t := by
  rw [ofReal_mul, ofReal_pow, ← Complex.mul_conj']
  simp only [mrtExponentialPolynomial, map_sum, sum_mul, mul_sum]
  rw [sum_comm (s := S) (t := S)]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [map_mul]
  have hp := mrt_phase_pair (freq i * t) (freq j * t)
  have he : (((freq i - freq j) * t : ℝ) : ℂ) * Complex.I =
      ((freq i * t - freq j * t : ℝ) : ℂ) * Complex.I := by congr 1; push_cast; ring
  dsimp only [mrtMeanSquareKernel]
  rw [he, ← hp]
  ring

lemma mrt_weighted_square_integrable {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
  have hi : Integrable (fun t : ℝ => ∑ i ∈ S, ∑ j ∈ S,
      (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
  have he : (fun t : ℝ => ∑ i ∈ S, ∑ j ∈ S,
      (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t) =
      fun t => ((Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    exact (mrt_weighted_square_expansion S a freq T t).symm
  rw [he] at hi
  simpa only [RCLike.re_to_complex, ofReal_re] using hi.re

/-- Exact finite mean-square formula.  This identity is valid for arbitrary
real frequencies; separation is needed only for the subsequent bound. -/
theorem mrt_weighted_mean_square {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)).re *
        (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
  have he : (∫ t : ℝ, ((Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)) *
        ((2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2) : ℝ) : ℂ) := by
    simp_rw [mrt_weighted_square_expansion]
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply sum_congr rfl
        intro j _
        rw [integral_const_mul, integral_mrtMeanSquareKernel hT]
      · intro j _
        exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
    · intro i _
      apply integrable_finsetSum
      intro j _
      exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
  rw [integral_complex_ofReal] at he
  have hr := congrArg Complex.re he
  simpa only [ofReal_re, Complex.re_sum, mul_re, ofReal_im, mul_zero, sub_zero] using hr

/-- The exact integral is bounded by the positive kernel quadratic form. -/
lemma mrt_weighted_mean_square_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖a i‖ * ‖a j‖ *
        (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
  rw [mrt_weighted_mean_square S a freq hT]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simpa only [norm_mul, norm_conj] using Complex.re_le_norm (a i * conj (a j))

/-- A symmetric positive kernel is bounded on the squared norm by its
largest row sum.  The numerical row estimate is proved separately. -/
lemma mrt_symmetric_row_bound {ι : Type*} (S : Finset ι) (K : ι → ι → ℝ)
    (v : ι → ℝ) (C : ℝ) (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, v i * v j * K i j) ≤ C * ∑ i ∈ S, (v i) ^ 2 := by
  have he : (∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j) =
      ∑ i ∈ S, (v i) ^ 2 * ∑ j ∈ S, K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S) (f := fun i j => (v j) ^ 2 / 2 * K i j)]
    simp only [← mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hk : (∑ j ∈ S, K j i) = ∑ j ∈ S, K i j :=
      sum_congr rfl fun j hj => hsymm j hj i hi
    rw [hk]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hK i hi j hj)
      nlinarith [sq_nonneg (v i - v j)]
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

theorem mrt_weighted_mean_square_of_rows {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T C : ℝ} (hT : 0 < T)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, 2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) ≤ C) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      C * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  apply (mrt_weighted_mean_square_le S a freq hT).trans
  apply mrt_symmetric_row_bound S _ (fun i => ‖a i‖) C
    (fun _ _ _ _ => by positivity) _ hrow
  intro i _ j _
  rw [show (freq i - freq j) ^ 2 = (freq j - freq i) ^ 2 by ring]

lemma mrtExponentialPolynomial_continuous {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) : Continuous (mrtExponentialPolynomial S a freq) := by
  unfold mrtExponentialPolynomial
  fun_prop

lemma mrt_unweighted_mean_square_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 := by
  have hf := (mrtExponentialPolynomial_continuous S a freq).norm.pow 2
  have hi := mrt_weighted_square_integrable S a freq hT
  have hc : Continuous (fun t : ℝ => Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
    exact (Real.continuous_exp.comp (continuous_abs.neg.div_const T)).mul hf
  have hb : -T ≤ T := by linarith
  calc
    _ ≤ ∫ t in -T..T, Real.exp 1 * (Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on hb (hf.intervalIntegrable (-T) T)
        ((continuous_const.mul hc).intervalIntegrable (-T) T)
      intro t ht
      have hat : |t| ≤ T := abs_le.mpr ht
      have hh : 0 ≤ 1 + -|t| / T := by
        have := (div_le_one hT).mpr hat
        rw [neg_div]
        linarith
      have he : 1 ≤ Real.exp 1 * Real.exp (-|t| / T) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp hh
      change ‖mrtExponentialPolynomial S a freq t‖ ^ 2 ≤
        Real.exp 1 * (Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2)
      nlinarith [sq_nonneg ‖mrtExponentialPolynomial S a freq t‖]
    _ = Real.exp 1 * ∫ t in -T..T, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le hb]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun t => by positivity)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare
namespace OAI

/-! The normalized dyadic Dirichlet-polynomial mean-value estimate used in
corrected MRT Appendix A.  The coefficient bound is completely arbitrary. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators

theorem mrt_dirichlet_mean_square_subset (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hrow : ∀ m ∈ S,
      (∑ n ∈ S, 2 * T /
        (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2)) ≤
          8 * (T + (N : ℝ)) := by
    intro m hm
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
      _ = ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2) := by
        apply sum_congr rfl
        intro n _
        have he (a b : ℝ) : (-a - -b) ^ 2 = (a - b) ^ 2 := by ring
        simp only [he]
      _ ≤ _ := mrt_logarithmic_kernel_row hT (hS hm)
  calc
    _ ≤ Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2 :=
      mrt_unweighted_mean_square_le _ _ _ hT
    _ ≤ Real.exp 1 * (8 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mrt_weighted_mean_square_of_rows _ _ _ hT hrow)
        (Real.exp_pos _).le
    _ = _ := by ring





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitCorrection
namespace OAI

/-! The exact convolution with the constant-one function used for the
near-twist renormalization. Its prime coefficients are the actual deviation
from one, including missing-prime masks. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



@[simp] lemma halaszUnitCorrectionLocal_zero (F : ℕ → ℂ) (p : ℕ) :
    halaszUnitCorrectionLocal F p 0 = 1 := by simp [halaszUnitCorrectionLocal]









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRestrictedEnergy
namespace OAI

/-! Finite energy bounds on arbitrary measurable frequency classes.
They retain the explicit coarse-bin count and permit the coefficient
bounds to vary from bin to bin. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_continuous_square_integrable {F : ℝ → ℂ} (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    IntegrableOn (fun t => ‖F t‖ ^ 2) E := by
  have hi : IntegrableOn (fun t => ‖F t‖ ^ 2) (Set.Ioc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      ((hF.norm.pow 2).intervalIntegrable _ _)
  exact hi.mono_set hE

lemma mrt_restricted_square_le_interval {F : ℝ → ℂ} (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖F t‖ ^ 2) ≤ ∫ t in -T..T, ‖F t‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact setIntegral_mono_set
    (mrt_continuous_square_integrable hF hT (Set.Subset.refl _))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall hE)


/-- Split a polynomial into a coarse approximation and its actual error
on a frequency class, bounding only the error by its full-interval energy. -/
theorem mrt_restricted_energy_split (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖F t‖ ^ 2) ≤
      2 * (∫ t in -T..T, ‖F t - G t‖ ^ 2) + 2 * (∫ t in E, ‖G t‖ ^ 2) := by
  have hiG := mrt_continuous_square_integrable hG hT hE
  have hiD : IntegrableOn (fun t => ‖F t - G t‖ ^ 2) E :=
    mrt_continuous_square_integrable (hF.sub hG) hT hE
  calc
    _ ≤ ∫ t in E, (2 * ‖F t - G t‖ ^ 2 + 2 * ‖G t‖ ^ 2) := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((hiD.const_mul 2).add (hiG.const_mul 2))
      intro t _
      change ‖F t‖ ^ 2 ≤ 2 * ‖F t - G t‖ ^ 2 + 2 * ‖G t‖ ^ 2
      have ht := norm_add_le (F t - G t) (G t)
      rw [sub_add_cancel] at ht
      nlinarith [sq_nonneg (‖F t - G t‖ - ‖G t‖), norm_nonneg (F t),
        norm_nonneg (F t - G t), norm_nonneg (G t)]
    _ = 2 * (∫ t in E, ‖F t - G t‖ ^ 2) + 2 * (∫ t in E, ‖G t‖ ^ 2) := by
      rw [integral_add (hiD.const_mul 2) (hiG.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (mrt_restricted_square_le_interval (hF.sub hG) hT hE) (by norm_num)) le_rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRamareIdentity
namespace OAI

/-! The corrected Ramaré identity from MRT v3, equation (3.2).
The denominator retains `1_{p ∤ m}`; repeated prime factors are allowed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma finitePrimeDivisorCount_eq_card (P : Finset ℕ) (n : ℕ) :
    finitePrimeDivisorCount P n = (P.filter (fun p => p ∣ n)).card := by
  simp [finitePrimeDivisorCount, sum_boole]












end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse
namespace OAI

/-! Coarse Ramaré factorization on the actual typical-factorization set.
Removing a prime from the selected band leaves precisely the other-band
mask; the square and endpoint errors retain their uniform finite bounds. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrtTypicalCoefficient_oneBounded {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) :
    OneBounded (mrtTypicalCoefficient J P F) := by
  intro n hn
  unfold mrtTypicalCoefficient
  split_ifs
  · exact hF n hn
  · simp





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeBands
namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The reciprocal-mass bounds follow from Mertens’ theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma mrtPrimeBand_prime {P Q : ℝ} {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : p.Prime :=
  sievePrimesUpTo_prime Q p (mem_sdiff.mp hp).1

lemma mrtPrimeBand_bounds {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : P < p ∧ (p : ℝ) ≤ Q := by
  have hpQ := (mem_sdiff.mp hp).1
  have hpP := (mem_sdiff.mp hp).2
  refine ⟨?_, sievePrimesUpTo_le Q hQ p hpQ⟩
  by_contra hnot
  have hple : (p : ℝ) ≤ P := le_of_not_gt hnot
  exact hpP (mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hP).mpr hple),
    mrtPrimeBand_prime hp⟩)




end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszExceptionalEnergy
namespace OAI

/-! The near-frequency exceptional set can be controlled in mean square
without paying for the width of that frequency interval. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_dyadic_sub (F G : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    mrtDyadicPolynomial (fun n => F n - G n) N t =
      mrtDyadicPolynomial F N t - mrtDyadicPolynomial G N t := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  simp only [sub_div, sub_mul, sum_sub_distrib]

lemma halasz_exceptional_coefficient_mass {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Ioc N (2 * N),
      ‖(F n - mrtTypicalCoefficient J P F n) / (n : ℂ)‖ ^ 2) ≤
      (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N ^ 2 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    _ ≤ ∑ n ∈ Ioc N (2 * N), if ¬mrtTypical J P n then (1 / (N : ℝ)) ^ 2 else 0 := by
      apply sum_le_sum
      intro n hn
      have hn0 : 0 < n := hN.trans (mem_Ioc.mp hn).1
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
      by_cases ht : mrtTypical J P n
      · simp [mrtTypicalCoefficient, ht]
      · simp only [mrtTypicalCoefficient, ht, ite_false, sub_zero, not_false_eq_true, ite_true]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        rw [norm_div, Complex.norm_natCast]
        exact (div_le_div_of_nonneg_right (hF n hn0) (by positivity)).trans
          (one_div_le_one_div_of_le hNr hnR)
    _ = _ := by rw [← sum_filter]; simp [div_eq_mul_inv]

/-- The error from excluding atypical integers costs their density, even
when the near-frequency interval grows. -/
theorem halasz_exceptional_dyadic_energy {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial F N t -
        mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      8 * Real.exp 1 * (T / N + 2) *
        (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm := mrt_dirichlet_mean_square_subset (Ioc N (2 * N))
    (N := 2 * N) (by
      intro n hn
      exact mem_Ioc.mpr ⟨lt_trans hN (mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2⟩)
    (fun n => (F n - mrtTypicalCoefficient J P F n) / (n : ℂ)) hT
  change (∫ t in -T..T, ‖mrtDyadicPolynomial
    (fun n => F n - mrtTypicalCoefficient J P F n) N t‖ ^ 2) ≤ _ at hm
  simp_rw [halasz_dyadic_sub] at hm
  apply hm.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + ((2 * N : ℕ) : ℝ)) *
        ((((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N ^ 2) :=
      mul_le_mul_of_nonneg_left (halasz_exceptional_coefficient_mass J P F hF hN) (by positivity)
    _ = _ := by push_cast; field_simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalCount
namespace OAI

/-! The exact dyadic atypical count in terms of the translated probability
used by the proved MRT density theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_typical_dyadic_count {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (N : ℕ) [NeZero N] :
    (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) =
      (N : ℝ) * (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical J P (N + 1 + n.val)) := by
  unfold FiniteLaw.probability FiniteLaw.average uniformFiniteLaw
  dsimp only
  rw [← mul_sum, Fintype.card_fin, ← mul_assoc]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [mul_one_div_cancel hN, one_mul]
  calc
    _ = ∑ n ∈ Ioc N (2 * N), if ¬mrtTypical J P n then (1 : ℝ) else 0 := by
      rw [← sum_filter]
      simp
    _ = _ := by
      symm
      apply sum_bij (fun n : Fin N => fun _ => N + 1 + n.val)
      · intro n _
        apply mem_Ioc.mpr
        have hn := n.isLt
        omega
      · intro n _ m _ he
        apply Fin.ext
        omega
      · intro n hn
        refine ⟨⟨n - (N + 1), ?_⟩, mem_univ _, ?_⟩
        · have hn := mem_Ioc.mp hn
          omega
        · have hn := mem_Ioc.mp hn
          change N + 1 + (n - (N + 1)) = n
          omega
      · intro n _
        simp

lemma halasz_typical_dyadic_density_bound {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) {N : ℕ} [NeZero N] (δ : ℝ)
    (hδ : (uniformFiniteLaw (Fin N)).probability
      (fun n => ¬mrtTypical J P (N + 1 + n.val)) ≤ δ) :
    (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N ≤ δ := by
  rw [halasz_typical_dyadic_count]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simpa [mul_div_cancel_left₀ _ hNr] using hδ

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogPrimeBins
namespace OAI

/-! Actual logarithmic bins used in the MRT factorization. Their integer
index and multiplicative width are controlled with the original floor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma mrt_prime_log_bin_bounds {H : ℝ} (hH : 0 < H) {p : ℕ} (hp : 1 ≤ p) :
    mrtPrimeLogLower H (mrtPrimeLogBin H p) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (1 / H) * mrtPrimeLogLower H (mrtPrimeLogBin H p) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp1
  have hlo : (mrtPrimeLogBin H p : ℝ) ≤ H * Real.log p :=
    Nat.floor_le (mul_nonneg hH.le (Real.log_nonneg hp1))
  have hhi : H * Real.log p < (mrtPrimeLogBin H p : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · calc
      _ ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr
        ((div_le_iff₀ hH).mpr (by nlinarith))
      _ = _ := Real.exp_log hp0
  · calc
      (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log hp0).symm
      _ ≤ Real.exp (1 / H + (mrtPrimeLogBin H p : ℝ) / H) := by
        apply Real.exp_le_exp.mpr
        rw [← add_div]
        apply (le_div_iff₀ hH).mpr
        nlinarith
      _ = _ := by rw [Real.exp_add]; rfl

lemma mrt_prime_log_bin_range {H P Q : ℝ} (hH : 0 ≤ H)
    (hP : 0 < P) {p : ℕ} (hp : P ≤ p) (hq : (p : ℝ) ≤ Q) :
    mrtPrimeLogBin H p ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊ := by
  have hp0 : (0 : ℝ) < p := hP.trans_le hp
  apply mem_Icc.mpr
  constructor
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.log_le_log hP hp) hH)
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hq) hH)

lemma mrt_prime_log_width {H : ℝ} (hH : 2 ≤ H) :
    1 ≤ Real.exp (1 / H) ∧ Real.exp (1 / H) ≤ 2 ∧
      Real.exp (1 / H) - 1 ≤ 2 / H := by
  have hH0 : 0 < H := by linarith
  have hi0 : (0 : ℝ) ≤ 1 / H := by positivity
  have hi : (1 : ℝ) / H ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hH
  have he := Real.exp_bound' hi0 (show (1 : ℝ) / H ≤ 1 by linarith) (n := 1) (by norm_num)
  norm_num at he
  have he' : Real.exp (1 / H) ≤ 1 + (1 / H) * 2 := by simpa only [one_div] using he
  refine ⟨Real.one_le_exp hi0, ?_, ?_⟩
  · nlinarith [he']
  · simpa only [div_eq_mul_inv, one_mul] using
      (show Real.exp (1 / H) - 1 ≤ 2 * (1 / H) by linarith [he'])

lemma mrt_prime_log_lower_le_upper {H Q : ℝ} (hH : 0 < H) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : k ≤ ⌊H * Real.log Q⌋₊) : mrtPrimeLogLower H k ≤ Q := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hf : (⌊H * Real.log Q⌋₊ : ℝ) ≤ H * Real.log Q :=
    Nat.floor_le (mul_nonneg hH.le (Real.log_nonneg hQ))
  have hkR : (k : ℝ) ≤ ⌊H * Real.log Q⌋₊ := by exact_mod_cast hk
  calc
    _ ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr
      ((div_le_iff₀ hH).mpr (by nlinarith))
    _ = _ := Real.exp_log hQ0



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogBinEndpoints
namespace OAI

/-! Endpoint control for every logarithmic bin, including the first
partially filled bin below the original lower endpoint. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma mrt_log_bin_lower_endpoint {H P : ℝ} (hH : 1 ≤ H) (hP : 0 < P)
    {k : ℕ} (hk : ⌊H * Real.log P⌋₊ ≤ k) :
    Real.exp (-1) * P ≤ mrtPrimeLogLower H k := by
  have hH0 : 0 < H := by linarith
  have hkR : (⌊H * Real.log P⌋₊ : ℝ) ≤ k := by exact_mod_cast hk
  have hf : H * Real.log P < (k : ℝ) + 1 :=
    (Nat.lt_floor_add_one (H * Real.log P)).trans_le (by linarith)
  have hi : (1 : ℝ) / H ≤ 1 := (div_le_one hH0).mpr hH
  have hl : Real.log P - 1 ≤ (k : ℝ) / H := by
    have hh : Real.log P < ((k : ℝ) + 1) / H :=
      (lt_div_iff₀ hH0).mpr (by nlinarith)
    rw [add_div] at hh
    linarith
  calc
    _ = Real.exp (Real.log P - 1) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hP]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hl



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogClassData
namespace OAI

/-! Literal logarithmic prime polynomials and their small/large frequency
sets. These sets supply the hypotheses of the general cofactor estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical




lemma mrt_log_prime_polynomial_continuous (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (k : ℕ) : Continuous (mrtLogPrimePolynomial S F H k) :=
  mrtExponentialPolynomial_continuous _ _ _




lemma mrt_log_bin_prime_data (S : Finset ℕ) {H P Q : ℝ} (hH : 2 ≤ H)
    (hP : 0 < P) (hprime : ∀ p ∈ S, p.Prime)
    (hrange : ∀ p ∈ S, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Q) :
    (∀ p ∈ S, mrtPrimeLogBin H p ∈ mrtLogBins H P Q) ∧
    (∀ p ∈ S, mrtPrimeLogLower H (mrtPrimeLogBin H p) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (1/H)*mrtPrimeLogLower H (mrtPrimeLogBin H p)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    exact mrt_prime_log_bin_range (by linarith) hP (hrange p hp).1 (hrange p hp).2
  · intro p hp
    exact mrt_prime_log_bin_bounds (by linarith) (hprime p hp).one_le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtractionErrors
namespace OAI

/-! The prime-square and coarse-bin errors sum independently of the
number of MRT bands. The only input is their actual lower endpoints. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_finite_reciprocal_square_tail (S : Finset ℕ) {y : ℝ} (hy : 1 ≤ y)
    (hS : ∀ n ∈ S, y ≤ (n:ℝ)) : (∑ n ∈ S, 1/(n:ℝ)^2) ≤ 2/y := by
  let k := ⌈y⌉₊-1
  have hc : 1 ≤ ⌈y⌉₊ := by
    exact_mod_cast hy.trans (Nat.le_ceil y)
  have hk : k+1 = ⌈y⌉₊ := by dsimp [k]; omega
  have hsub : S ⊆ Ioo k (S.sup id+1) := by
    intro n hn
    have hcn : ⌈y⌉₊ ≤ n := Nat.ceil_le.mpr (hS n hn)
    exact mem_Ioo.mpr ⟨by dsimp [k]; omega, Nat.lt_succ_of_le (le_sup (f := id) hn)⟩
  calc
    _ ≤ ∑ n ∈ Ioo k (S.sup id+1), ((n:ℝ)^2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2/((k:ℝ)+1) := sum_Ioo_inv_sq_le (α := ℝ) k (S.sup id+1)
    _ = 2/(⌈y⌉₊:ℝ) := by
      have hkr : (k:ℝ)+1 = (⌈y⌉₊:ℝ) := by exact_mod_cast hk
      rw [hkr]
    _ ≤ 2/y := div_le_div_of_nonneg_left (by norm_num) (by linarith) (Nat.le_ceil y)


lemma mrt_prime_extraction_error (S : Finset ℕ) {y H : ℝ} (hH : 2 ≤ H)
    (hHy : H ≤ y) (hS : ∀ n ∈ S, y ≤ (n:ℝ)) :
    (∑ n ∈ S, 1/(n:ℝ)^2)+(∑ n ∈ S, 1/(n:ℝ)^2)^2+2/H ≤ 6/H := by
  let A := ∑ n ∈ S, 1/(n:ℝ)^2
  have hA0 : 0 ≤ A := sum_nonneg (fun _ _ => by positivity)
  have hA : A ≤ 2/H := (mrt_finite_reciprocal_square_tail S (by linarith) hS).trans
    (div_le_div_of_nonneg_left (by norm_num) (by linarith) hHy)
  have hA1 : A ≤ 1 := hA.trans ((div_le_one (by linarith : 0 < H)).mpr hH)
  have hs : A^2 ≤ A := by nlinarith
  change A+A^2+2/H ≤ 6/H
  have he : 6/H = 3*(2/H) := by ring
  rw [he]
  linarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraBandGeometry
namespace OAI

/-! The additional large-prime interval used after the last ordinary
band. A factor two in its lower logarithm absorbs bin rounding. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.Classical




theorem mrt_extra_band_geometry :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ mrtExtraPrimeResolution L ∧
      Real.exp (Real.sqrt L) < mrtExtraPrimeLower L ∧
      mrtExtraPrimeLower L ≤ mrtExtraPrimeUpper L ∧
      mrtExtraPrimeUpper L ≤ Real.exp (L/1000) ∧
      ∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L)
        (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L),
      1 < mrtPrimeLogLower (mrtExtraPrimeResolution L) k ∧
      L^(79/80:ℝ) ≤ Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) ∧
      Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) ≤ L := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/80 by norm_num)).bound
    (show (0:ℝ)<1/2 by norm_num)
  have hres := (tendsto_rpow_atTop (show (0:ℝ)<1/80 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hb,hres,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ))]
    with L hb hres hL hLL
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg hlogL.le,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hsmall : 2*Real.log L ≤ L^(1/80:ℝ) := by linarith
  have hpow : 1 ≤ L^(79/80:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hmul : L^(79/80:ℝ)*L^(1/80:ℝ)=L := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hPQ : mrtExtraPrimeLower L ≤ mrtExtraPrimeUpper L := by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hlogL).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hL0.le (79/80))
    rw [hmul] at hh
    nlinarith
  have hsep : Real.exp (Real.sqrt L) < mrtExtraPrimeLower L := by
    apply Real.exp_lt_exp.mpr
    have hh : Real.sqrt L ≤ L^(79/80:ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    linarith
  have hupper : mrtExtraPrimeUpper L ≤ Real.exp (L/1000) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left hL0.le (by norm_num) hLL
  refine ⟨hres,hsep,hPQ,hupper,?_⟩
  intro k hk
  let Y := mrtPrimeLogLower (mrtExtraPrimeResolution L) k
  have hYlow : L^(79/80:ℝ) ≤ Real.log Y := by
    have hh := mrt_log_bin_lower_endpoint (show 1 ≤ mrtExtraPrimeResolution L by
      change 1 ≤ L^(1/80:ℝ)
      linarith)
      (Real.exp_pos _) (mem_Icc.mp hk).1
    have hh' := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hh
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp] at hh'
    simp only [Real.log_exp] at hh'
    change -1+2*L^(79/80:ℝ) ≤ Real.log Y at hh'
    linarith
  have hY : 1 < Y := by
    change 1 < Real.exp ((k:ℝ)/mrtExtraPrimeResolution L)
    apply Real.one_lt_exp_iff.mpr
    have hh : 0 < Real.log Y := by linarith
    simpa only [Y,mrtPrimeLogLower,Real.log_exp] using hh
  have hQ1 : 1 ≤ mrtExtraPrimeUpper L := Real.one_le_exp (by positivity)
  have hYhi := mrt_prime_log_lower_le_upper (show 0 < mrtExtraPrimeResolution L by
    change 0 < L^(1/80:ℝ)
    linarith)
    hQ1 (mem_Icc.mp hk).2
  have hl : Real.log Y ≤ L/Real.log L := by
    simpa only [mrtExtraPrimeUpper,Real.log_exp] using
      Real.log_le_log (show 0 < Y by linarith) hYhi
  exact ⟨hY,hYlow,hl.trans (div_le_self hL0.le (by linarith))⟩

/-- The additional interval is disjoint from every original prime set
under the proved maximal-band upper cutoff. -/
theorem mrt_extra_band_disjoint :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, (p:ℝ) ≤ Real.exp (Real.sqrt L)) →
      Disjoint S (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) := by
  filter_upwards [mrt_extra_band_geometry] with L hL
  intro S hS
  apply disjoint_left.mpr
  intro p hp hq
  have hh := (mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hq).1
  have hs := hS p hp
  have hsep : Real.exp (Real.sqrt L) < Real.exp (2*L^(79/80:ℝ)) := hL.2.1
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraMissing
namespace OAI

/-! The actual additional-band sieve controls the dyadic coefficient
error before any frequency partition or sampling. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_single_band_not_typical (P : Finset ℕ) (n : ℕ) :
    ¬mrtTypical ({()} : Finset Unit) (fun _ => P) n ↔ mrtPrimeAvoids P n := by
  simp [mrtTypical, mrtPrimeAvoids]

lemma mrt_supported_eq_single_band (P : Finset ℕ) (F : ℕ → ℂ) :
    mrtSupportedCoefficient P F =
      mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F := by
  funext n
  have hz : finitePrimeDivisorCount P n=0 ↔ mrtPrimeAvoids P n := by
    rw [finitePrimeDivisorCount_eq_card, card_eq_zero]
    simp only [eq_empty_iff_forall_notMem, mem_filter, not_and, mrtPrimeAvoids]
  have ht := mrt_single_band_not_typical P n
  by_cases h : mrtTypical ({()} : Finset Unit) (fun _ => P) n
  · have ha : ¬mrtPrimeAvoids P n := fun ha => (ht.mpr ha) h
    simp [mrtSupportedCoefficient, mrtTypicalCoefficient, hz, ha, h]
  · have ha : mrtPrimeAvoids P n := ht.mp h
    simp [mrtSupportedCoefficient, mrtTypicalCoefficient, hz, ha, h]

lemma mrt_avoiding_dyadic_density (P : Finset ℕ) {N : ℕ} [NeZero N]
    (δ : ℝ) (hδ : (uniformFiniteLaw (Fin N)).probability
      (fun n => mrtPrimeAvoids P (N+1+n.val)) ≤ δ) :
    (((Ioc N (2*N)).filter (fun n => mrtPrimeAvoids P n)).card:ℝ)/N ≤ δ := by
  have hh := halasz_typical_dyadic_density_bound ({()} : Finset Unit)
    (fun _ => P) δ (by simpa only [mrt_single_band_not_typical] using hδ)
  simpa only [mrt_single_band_not_typical] using hh

/-- One additional missing-band error costs only its actual density,
with a constant independent of the number of original typical bands. -/
theorem mrt_extra_missing_energy : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in Filter.atTop, ∀ (F : ℕ → ℂ), OneBounded F →
    ∀ (N : ℕ), Real.exp L ≤ N → ∀ T : ℝ, 0 < T →
      (∫ t in -T..T, ‖mrtDyadicPolynomial F N t -
        mrtDyadicPolynomial (mrtSupportedCoefficient
          (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F) N t‖^2) ≤
        C*(T/N+1)*(Real.log L/L^(1/80:ℝ)) := by
  obtain ⟨C,hC,hprob⟩ := mrt_extra_prime_avoidance
  refine ⟨16*Real.exp 1*C,by positivity,?_⟩
  filter_upwards [hprob,Filter.eventually_ge_atTop (1:ℝ)] with L hprob hL
  intro F hF N hN T hT
  have hN0 : (0:ℝ) < N := (Real.exp_pos L).trans_le hN
  have hNn : 0 < N := by exact_mod_cast hN0
  let : NeZero N := ⟨hNn.ne'⟩
  let P := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let d : ℝ := (((Ioc N (2*N)).filter (fun n => mrtPrimeAvoids P n)).card:ℝ)/N
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd : d ≤ C*(Real.log L/L^(1/80:ℝ)) := by
    exact mrt_avoiding_dyadic_density P _ (by
      simpa only [mul_div_assoc] using hprob (N+1) N hN)
  have hh := halasz_exceptional_dyadic_energy ({()} : Finset Unit)
    (fun _ => P) F hF hNn hT
  rw [← mrt_supported_eq_single_band] at hh
  simp only [mrt_single_band_not_typical] at hh
  change (∫ t in -T..T, ‖mrtDyadicPolynomial F N t -
    mrtDyadicPolynomial (mrtSupportedCoefficient P F) N t‖^2) ≤ _
  have hr : 0 ≤ T/(N:ℝ) := div_nonneg hT.le hN0.le
  calc
    _ ≤ 8*Real.exp 1*(T/N+2)*d := by
      simpa only [d,mul_div_assoc] using hh
    _ ≤ 16*Real.exp 1*(T/N+1)*d := by
      nlinarith [mul_nonneg (mul_nonneg (Real.exp_pos 1).le hd0) hr]
    _ ≤ 16*Real.exp 1*(T/N+1)*(C*(Real.log L/L^(1/80:ℝ))) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraFactorization
namespace OAI

/-! Complete additional-prime factorization of the actual typical
polynomial. The missing-band, prime-square and bin-boundary errors are
summed once, independently of the frequency classes. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrt_extra_coarse_continuous {ι : Type*} (L : ℝ) (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (N : ℕ) :
    Continuous (mrtExtraCoarsePolynomial L J P F N) := by
  apply continuous_finsetSum
  intro k _
  exact (mrt_log_prime_polynomial_continuous _ _ _ _).mul
    (mrtCofactorPolynomial_continuous _ _ _ _)

theorem mrt_extra_factorization_energy : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in Filter.atTop, ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) →
      (∀ j ∈ J, ∀ p ∈ P j, (p:ℝ) ≤ Real.exp (Real.sqrt L)) →
    ∀ F : ℕ → ℂ, Multiplicative F → OneBounded F →
    ∀ N : ℕ, Real.exp L ≤ N → ∀ T : ℝ, 0 < T →
      (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t -
        mrtExtraCoarsePolynomial L J P F N t‖^2) ≤
        C*(T/N+1)*(Real.log L/L^(1/80:ℝ)) := by
  obtain ⟨C,hC,hmissing⟩ := mrt_extra_missing_energy
  refine ⟨2*C+16896*Real.exp 1,by positivity,?_⟩
  filter_upwards [hmissing,mrt_extra_band_geometry,mrt_extra_band_disjoint,
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with L hmissing hg hdis hL hlog
  intro ι J P hp hmax F hF hFb N hN T hT
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  let B := mrtTypicalCoefficient J P F
  let K := mrtLogBins H (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded J P F hFb
  have hN0 : (0:ℝ) < N := (Real.exp_pos L).trans_le hN
  have hNn : 0 < N := by exact_mod_cast hN0
  have hL0 : 0 < L := by linarith
  have hH : 2 ≤ H := hg.1
  have hH0 : 0 < H := by linarith
  have hA : ∀ p ∈ A, p.Prime := fun _ hp => mrtPrimeBand_prime hp
  have hAout : Disjoint A (J.biUnion P) := by
    apply Disjoint.symm
    apply hdis
    intro p hp'
    obtain ⟨j,hj,hpj⟩ := mem_biUnion.mp hp'
    exact hmax j hj p hpj
  have hrange : ∀ p ∈ A, mrtExtraPrimeLower L ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtExtraPrimeUpper L := by
    intro p hp'
    have hh := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp'
    exact ⟨hh.1.le,hh.2⟩
  have hd := mrt_log_bin_prime_data A hH (Real.exp_pos _) hA hrange
  have hw := mrt_prime_log_width hH
  have hm := mrt_extra_prime_mean_square J P hp A hA hAout K (mrtPrimeLogBin H)
    hd.1 (mrtPrimeLogLower H) hNn hw.1 hw.2.1 hd.2 F hF hFb hT
  change (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t -
    mrtExtraCoarsePolynomial L J P F N t‖^2) ≤ _ at hm
  have hHP : H ≤ mrtExtraPrimeLower L := by
    calc
      H ≤ Real.sqrt L := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ Real.exp (Real.sqrt L) := by linarith [Real.add_one_le_exp (Real.sqrt L)]
      _ ≤ mrtExtraPrimeLower L := hg.2.1.le
  have herr := mrt_prime_extraction_error A hH hHP (fun p hp' => (hrange p hp').1)
  have hs : (∑ p ∈ A, 1/(p:ℝ)^2)+(∑ p ∈ A, 1/(p:ℝ)^2)^2+
      (Real.exp (1/H)-1) ≤ 6/H := by linarith [hw.2.2]
  have hnorm : 1/H ≤ Real.log L/L^(1/80:ℝ) := by
    change 1/H ≤ Real.log L/H
    exact div_le_div_of_nonneg_right hlog hH0.le
  have hfactor : 0 ≤ 1408*Real.exp 1*(T/(N:ℝ)+1) := by positivity
  have hm' : (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t -
      mrtExtraCoarsePolynomial L J P F N t‖^2) ≤
        (8448*Real.exp 1)*(T/N+1)*(Real.log L/L^(1/80:ℝ)) := by
    apply hm.trans
    calc
      _ ≤ 1408*Real.exp 1*(T/(N:ℝ)+1)*(6/H) :=
        mul_le_mul_of_nonneg_left hs hfactor
      _ = (8448*Real.exp 1)*(T/N+1)*(1/H) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hm'':= hmissing B hB N hN T hT
  have hD : Continuous (mrtDyadicPolynomial B N) := mrtExponentialPolynomial_continuous _ _ _
  have hS : Continuous (mrtDyadicPolynomial (mrtSupportedCoefficient A B) N) :=
    mrtExponentialPolynomial_continuous _ _ _
  have hG := mrt_extra_coarse_continuous L J P F N
  have hh := mrt_restricted_energy_split
    (fun t => mrtDyadicPolynomial B N t-mrtExtraCoarsePolynomial L J P F N t)
    (fun t => mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t-
      mrtExtraCoarsePolynomial L J P F N t)
    (hD.sub hG) (hS.sub hG) hT.le (Set.Subset.refl (Set.Ioc (-T) T))
  have he (t : ℝ) :
      (mrtDyadicPolynomial B N t-mrtExtraCoarsePolynomial L J P F N t)-
      (mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t-
        mrtExtraCoarsePolynomial L J P F N t) =
      mrtDyadicPolynomial B N t-mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t := by ring
  simp only [he,← intervalIntegral.integral_of_le (show -T ≤ T by linarith)] at hh
  apply hh.trans
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left hm'' (by norm_num : (0:ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hm' (by norm_num : (0:ℝ) ≤ 2))
  convert (preTransparency := .instances) hsum using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallEnergy
namespace OAI

/-! No-small-class energy, including the complete extra-band extraction
error, under the sparse-prime estimate and the cofactor pointwise bound. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem mrt_no_small_energy_sharp_oai (hprime : HalaszPrimeSparseInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), Multiplicative F → OneBounded F →
    ∀ J j : ℕ, j < J →
    (∀ i ∈ Icc 1 J, ∀ p ∈ V i, p.Prime) →
    (∀ i ∈ Icc 1 J, ∀ p ∈ V i, (p:ℝ) ≤ Real.exp (Real.sqrt L)) →
    ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ N : ℕ, Real.exp L ≤ N → ∀ E : Set ℝ,
    MeasurableSet E → E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) →
    (∀ t ∈ E, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
        (mrtExtraPrimeUpper L), ∀ t ∈ E,
      L^(-100:ℝ) ≤ ‖mrtLogPrimePolynomial
        (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
          (mrtExtraPrimeResolution L) k t‖ →
      ‖mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
        (mrtTypicalCoefficient (Icc 1 J) V F) N
        (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖ ≤ 2*L^(-1/40:ℝ)) →
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2) ≤
      C*Real.log L/L^(1/80:ℝ) := by
  obtain ⟨C₀,hC₀,hcoarse⟩ := mrt_no_small_coarse_energy hprime
  obtain ⟨C₁,hC₁,hfactor⟩ := mrt_extra_factorization_energy
  refine ⟨2*C₀+4*C₁,by positivity,?_⟩
  filter_upwards [hcoarse,hfactor,Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with L hcoarse hfactor hL hlog
  intro V F hF hFb J j hj hp hmax P Q hP hPQ hQ hres hrange hlo hhi N hN E hE hET hno hpoint
  have hmem : j+1 ∈ Icc 1 J := mem_Icc.mpr ⟨by omega,by omega⟩
  have hc := hcoarse V F hFb J j hj P Q hP hPQ hQ hres (hp (j+1) hmem)
    hrange hlo hhi N hN E hE hET hno hpoint
  have hf := hfactor (Icc 1 J) V hp hmax F hF hFb N hN (Real.exp L) (Real.exp_pos L)
  have hN0 : (0:ℝ) < N := (Real.exp_pos L).trans_le hN
  have hratio : Real.exp L/(N:ℝ)+1 ≤ 2 := by
    have hh := (div_le_one hN0).mpr hN
    linarith
  have hL0 : 0 < L := by linarith
  have hd : 0 ≤ Real.log L/L^(1/80:ℝ) := by positivity
  have hf' : (∫ t in -Real.exp L..Real.exp L,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t-
        mrtExtraCoarsePolynomial L (Icc 1 J) V F N t‖^2) ≤
      2*C₁*(Real.log L/L^(1/80:ℝ)) := by
    apply hf.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hC₁.le) hd
    convert (preTransparency := .instances) hh using 1
    ring
  have hpower : L^(-1/80:ℝ) ≤ Real.log L/L^(1/80:ℝ) := by
    calc
      _ ≤ L^(-1/80:ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = 1/L^(1/80:ℝ) := by
        rw [show (-1/80:ℝ)=-(1/80:ℝ) by ring,Real.rpow_neg hL0.le]
        simp only [one_div]
      _ ≤ _ := div_le_div_of_nonneg_right hlog (by positivity)
  have hc' := hc.trans (mul_le_mul_of_nonneg_left hpower hC₀.le)
  have hs := mrt_restricted_energy_split
    (mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N)
    (mrtExtraCoarsePolynomial L (Icc 1 J) V F N)
    (mrtExponentialPolynomial_continuous _ _ _)
    (mrt_extra_coarse_continuous _ _ _ _ _) (Real.exp_pos L).le hET
  apply hs.trans
  have hh := add_le_add (mul_le_mul_of_nonneg_left hf' (by norm_num : (0:ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hc' (by norm_num : (0:ℝ) ≤ 2))
  convert (preTransparency := .instances) hh using 1
  ring




end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_no_small_energy_sharp_oai := @OAI.TwoPointCorrelations.mrt_no_small_energy_sharp_oai
