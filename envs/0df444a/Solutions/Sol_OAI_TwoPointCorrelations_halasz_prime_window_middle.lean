-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_prime_window_middle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:22:14.611286+00:00
-- url     : https://prove2.me/submissions/4f30f1b3-a033-4159-a6ce-e629db42d293

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_prime_log_window_bound

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

/-- The weighted frequency-row version of the finite mean-value theorem.
The coefficients are `a i * w i`, and only one copy of `w` remains on the
right.  Zero weights are allowed. -/
theorem halasz_weighted_mean_square_of_rows {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (w freq : ι → ℝ) {T C : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hrow : ∀ i ∈ S,
      ∑ j ∈ S, w j * (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) ≤ C) :
    (∫ t : ℝ, Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S (fun i => a i * (w i : ℂ)) freq t‖ ^ 2) ≤
      C * ∑ i ∈ S, ‖a i‖ ^ 2 * w i := by
  apply (mrt_weighted_mean_square_le S _ freq hT).trans
  have hn (i : ι) (hi : i ∈ S) : ‖a i * (w i : ℂ)‖ = ‖a i‖ * w i := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  have he : (∑ i ∈ S, ∑ j ∈ S, ‖a i * (w i : ℂ)‖ * ‖a j * (w j : ℂ)‖ *
      (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2))) =
      ∑ i ∈ S, ∑ j ∈ S, (‖a i‖ * w i) * (‖a j‖ * w j) *
      (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hn i hi, hn j hj]
  rw [he]
  apply halasz_weighted_symmetric_row_bound S _ w (fun i => ‖a i‖) C hw
    (fun _ _ _ _ => by positivity) _ hrow
  intro i _ j _
  rw [show (freq i - freq j) ^ 2 = (freq j - freq i) ^ 2 by ring]

/-- Unweighted time integration costs just the fixed factor `exp 1`. -/
theorem halasz_mean_square_of_weighted_rows {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (w freq : ι → ℝ) {T C : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hrow : ∀ i ∈ S,
      ∑ j ∈ S, w j * (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) ≤ C) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial S (fun i => a i * (w i : ℂ)) freq t‖ ^ 2) ≤
      Real.exp 1 * C * ∑ i ∈ S, ‖a i‖ ^ 2 * w i := by
  apply (mrt_unweighted_mean_square_le S _ freq hT).trans
  calc
    _ ≤ Real.exp 1 * (C * ∑ i ∈ S, ‖a i‖ ^ 2 * w i) :=
      mul_le_mul_of_nonneg_left
        (halasz_weighted_mean_square_of_rows S a w freq hT hw hrow) (Real.exp_pos _).le
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszFrequencyRows
namespace OAI

/-! A local frequency-mass estimate controls the entire quadratic-decay row.
This keeps the prime-counting input separate from the finite harmonic-analysis
argument, and applies to the actual finite Dirichlet polynomial. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical


lemma halasz_quadratic_kernel_sum (M : ℕ) :
    (∑ k ∈ range (M + 1), (1 + (k : ℝ) ^ 2)⁻¹) ≤ 4 := by
  have he : range (M + 1) = insert 0 (Ioc 0 M) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [he, sum_insert (by simp)]
  have hh := mrt_quadratic_gap_sum (R := 1) (by norm_num) M
  norm_num only [div_one] at hh
  norm_num only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), add_zero, inv_one]
  linarith

/-- Shell mass at frequency resolution `1/T` controls the whole Fourier
kernel row, uniformly in the number and placement of the frequencies. -/
theorem halasz_frequency_row_of_shells {ι : Type*} (S : Finset ι)
    (freq w : ι → ℝ) (u : ℝ) {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hshell : ∀ k : ℕ, ∑ i ∈ halaszFrequencyShell S freq T u k, w i ≤ B / T) :
    (∑ i ∈ S, w i * (2 * T / (1 + T ^ 2 * (freq i - u) ^ 2))) ≤ 8 * B := by
  classical
  let bin : ι → ℕ := fun i => Nat.floor (T * |freq i - u|)
  let M := S.sup bin
  have hmaps : ∀ i ∈ S, bin i ∈ range (M + 1) := by
    intro i hi
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := bin) hi))
  have hpoint (i : ι) :
      2 * T / (1 + T ^ 2 * (freq i - u) ^ 2) ≤
        2 * T * (1 + (bin i : ℝ) ^ 2)⁻¹ := by
    have hfloor : (bin i : ℝ) ≤ T * |freq i - u| :=
      Nat.floor_le (mul_nonneg hT.le (abs_nonneg _))
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (bin i)) hfloor 2
    rw [mul_pow, sq_abs] at hsq
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact inv_anti₀ (by positivity) (add_le_add le_rfl hsq)
  have hgroup : (∑ i ∈ S, w i * (2 * T * (1 + (bin i : ℝ) ^ 2)⁻¹)) =
      ∑ k ∈ range (M + 1), (2 * T * (1 + (k : ℝ) ^ 2)⁻¹) *
        ∑ i ∈ halaszFrequencyShell S freq T u k, w i := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    apply sum_congr rfl
    intro k _
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have he := (mem_filter.mp hi).2
    change bin i = k at he
    rw [he]
    ring
  calc
    _ ≤ ∑ i ∈ S, w i * (2 * T * (1 + (bin i : ℝ) ^ 2)⁻¹) := by
      exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hpoint i) (hw i hi))
    _ = _ := hgroup
    _ ≤ ∑ k ∈ range (M + 1), (2 * T * (1 + (k : ℝ) ^ 2)⁻¹) * (B / T) := by
      exact sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hshell k) (by positivity))
    _ = 2 * B * ∑ k ∈ range (M + 1), (1 + (k : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      field_simp
    _ ≤ 2 * B * 4 :=
      mul_le_mul_of_nonneg_left (halasz_quadratic_kernel_sum M) (by positivity)
    _ = _ := by ring



/-- A shell is the union of its two one-sided frequency intervals. -/
lemma halasz_shell_mass_of_windows {ι : Type*} (S : Finset ι)
    (freq w : ι → ℝ) (u : ℝ) {T A : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hwindow : ∀ v : ℝ,
      (∑ i ∈ S.filter (fun i => v ≤ freq i ∧ freq i ≤ v + 1 / T), w i) ≤ A / T)
    (k : ℕ) :
    (∑ i ∈ halaszFrequencyShell S freq T u k, w i) ≤ 2 * A / T := by
  classical
  let Q := halaszFrequencyShell S freq T u k
  let R := Q.filter (fun i => u ≤ freq i)
  let L := Q.filter (fun i => ¬u ≤ freq i)
  have he : Q = R ∪ L := by
    ext i
    simp only [R, L, mem_union, mem_filter]
    tauto
  have hd : Disjoint R L := by
    rw [disjoint_left]
    intro i hi hj
    exact (mem_filter.mp hj).2 (mem_filter.mp hi).2
  have hgap (i : ι) (hi : i ∈ Q) :
      (k : ℝ) / T ≤ |freq i - u| ∧ |freq i - u| ≤ ((k : ℝ) + 1) / T := by
    have heq := (mem_filter.mp hi).2
    change Nat.floor (T * |freq i - u|) = k at heq
    have hlo := Nat.floor_le (mul_nonneg hT.le (abs_nonneg (freq i - u)))
    have hhi := Nat.lt_floor_add_one (T * |freq i - u|)
    rw [heq] at hlo hhi
    constructor
    · exact (div_le_iff₀ hT).mpr (by linarith)
    · exact (le_div_iff₀ hT).mpr (by linarith)
  have hR : R ⊆ S.filter (fun i =>
      u + (k : ℝ) / T ≤ freq i ∧ freq i ≤ u + (k : ℝ) / T + 1 / T) := by
    intro i hi
    obtain ⟨hiQ, hiu⟩ := mem_filter.mp hi
    have hg := hgap i hiQ
    rw [abs_of_nonneg (sub_nonneg.mpr hiu)] at hg
    refine mem_filter.mpr ⟨(mem_filter.mp hiQ).1, ?_⟩
    simp only [add_div] at hg ⊢
    constructor <;> linarith
  have hL : L ⊆ S.filter (fun i =>
      u - ((k : ℝ) + 1) / T ≤ freq i ∧
        freq i ≤ u - ((k : ℝ) + 1) / T + 1 / T) := by
    intro i hi
    obtain ⟨hiQ, hiu⟩ := mem_filter.mp hi
    have hg := hgap i hiQ
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hiu))] at hg
    refine mem_filter.mpr ⟨(mem_filter.mp hiQ).1, ?_⟩
    simp only [add_div] at hg ⊢
    constructor <;> linarith
  have hbR : (∑ i ∈ R, w i) ≤ A / T := by
    apply (sum_le_sum_of_subset_of_nonneg hR ?_).trans (hwindow _)
    intro i hi _
    exact hw i (mem_filter.mp hi).1
  have hbL : (∑ i ∈ L, w i) ≤ A / T := by
    apply (sum_le_sum_of_subset_of_nonneg hL ?_).trans (hwindow _)
    intro i hi _
    exact hw i (mem_filter.mp hi).1
  change (∑ i ∈ Q, w i) ≤ _
  rw [he, sum_union hd]
  calc
    _ ≤ A / T + A / T := add_le_add hbR hbL
    _ = _ := by ring

/-- A uniform local frequency-mass bound gives a uniform kernel-row bound. -/
theorem halasz_frequency_row_of_windows {ι : Type*} (S : Finset ι)
    (freq w : ι → ℝ) (u : ℝ) {T A : ℝ} (hT : 0 < T) (hA : 0 ≤ A)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hwindow : ∀ v : ℝ,
      (∑ i ∈ S.filter (fun i => v ≤ freq i ∧ freq i ≤ v + 1 / T), w i) ≤ A / T) :
    (∑ i ∈ S, w i * (2 * T / (1 + T ^ 2 * (freq i - u) ^ 2))) ≤ 16 * A := by
  have hh := halasz_frequency_row_of_shells S freq w u hT (mul_nonneg (by norm_num) hA)
    hw (halasz_shell_mass_of_windows S freq w u hT hw hwindow)
  convert (preTransparency := .instances) hh using 1; ring

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPerronWindowKernel
namespace OAI

/-! A short multiplicative smoothing of Perron's kernel. The difference
has both the first-order bound and an integrable inverse-square tail. -/

namespace TwoPointCorrelations

open _root_.Complex


lemma halasz_exp_window_difference {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    ‖Complex.exp (((2 : ℂ) + (t : ℂ) * Complex.I) * (Real.log (1 + δ) : ℂ)) - 1‖ ≤
      δ * (3 + |t|) := by
  have hy : 0 < 1 + δ := by linarith
  have hlog0 : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (1 + δ) ≤ δ := by
    simpa only [add_sub_cancel_left] using Real.log_le_sub_one_of_pos hy
  let z := Complex.exp (((t * Real.log (1 + δ) : ℝ) : ℂ) * Complex.I)
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hz1 : ‖z - 1‖ ≤ |t| * Real.log (1 + δ) := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * Real.log (1 + δ))
    simpa only [z, mul_comm Complex.I, Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0] using h
  have he : Complex.exp (((2 : ℂ) + (t : ℂ) * Complex.I) *
      (Real.log (1 + δ) : ℂ)) = (((1 + δ) ^ 2 : ℝ) : ℂ) * z := by
    rw [show ((2 : ℂ) + (t : ℂ) * Complex.I) * (Real.log (1 + δ) : ℂ) =
      ((2 * Real.log (1 + δ) : ℝ) : ℂ) +
        (((t * Real.log (1 + δ) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp]
    congr 1
    exact_mod_cast (show Real.exp (2 * Real.log (1 + δ)) = (1 + δ) ^ 2 by
      simpa only [Nat.cast_ofNat, Real.exp_log hy] using Real.exp_nat_mul (Real.log (1 + δ)) 2)
  rw [he, show (((1 + δ) ^ 2 : ℝ) : ℂ) * z - 1 =
    (((1 + δ) ^ 2 - 1 : ℝ) : ℂ) * z + (z - 1) by push_cast; ring]
  calc
    _ ≤ ‖(((1 + δ) ^ 2 - 1 : ℝ) : ℂ) * z‖ + ‖z - 1‖ := norm_add_le _ _
    _ ≤ ((1 + δ) ^ 2 - 1) + |t| * Real.log (1 + δ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one,
        abs_of_nonneg (by nlinarith : 0 ≤ (1 + δ) ^ 2 - 1)]
      exact add_le_add le_rfl hz1
    _ ≤ δ * (3 + |t|) := by
      have hm := mul_le_mul_of_nonneg_left hlog (abs_nonneg t)
      nlinarith

lemma halasz_perron_window_factor {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (s : ℂ) :
    halaszPerronWindowKernel x δ s =
      (x : ℂ) ^ s * (Complex.exp ((s + 1) * (Real.log (1 + δ) : ℂ)) - 1) /
        ((δ : ℂ) * s * (s + 1)) := by
  have hy : 0 < 1 + δ := by linarith
  have hyexp : ((1 + δ : ℝ) : ℂ) * ((1 + δ : ℝ) : ℂ) ^ s =
      Complex.exp ((s + 1) * (Real.log (1 + δ) : ℂ)) := by
    calc
      _ = ((1 + δ : ℝ) : ℂ) ^ (s + 1) := by
        rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.cpow_one]
        ring
      _ = _ := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
          ← Complex.ofReal_log hy.le]
        congr 1
        ring
  unfold halaszPerronWindowKernel modFivePerronKernel
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le hx.le]
  calc
    _ = (x : ℂ) ^ s *
        (((1 + δ : ℝ) : ℂ) * ((1 + δ : ℝ) : ℂ) ^ s - 1) /
          ((δ : ℂ) * s * (s + 1)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hyexp]

theorem halasz_perron_window_bound {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (t : ℝ) :
    ‖halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ ≤
      4 * x / ‖1 + (t : ℂ) * Complex.I‖ := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have hs : 1 ≤ ‖s‖ := by simpa [s] using Complex.abs_re_le_norm s
  have hs1 : 2 ≤ ‖s + 1‖ := by
    have h := Complex.abs_re_le_norm (s + 1)
    norm_num [s] at h
    exact h
  have ht : |t| ≤ ‖s + 1‖ := by simpa [s] using Complex.abs_im_le_norm (s + 1)
  have hs0 : 0 < ‖s‖ := by linarith
  have hs10 : 0 < ‖s + 1‖ := by linarith
  have he : ‖Complex.exp ((s + 1) * (Real.log (1 + δ) : ℂ)) - 1‖ ≤
      δ * (4 * ‖s + 1‖) := by
    have he := halasz_exp_window_difference hδ hδ1 t
    have hshape : s + 1 = (2 : ℂ) + (t : ℂ) * Complex.I := by dsimp [s]; ring
    rw [hshape]
    apply he.trans
    have hnorm : 3 + |t| ≤ 4 * ‖s + 1‖ := by linarith
    rw [← hshape]
    exact mul_le_mul_of_nonneg_left hnorm hδ.le
  rw [halasz_perron_window_factor hx hδ, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  change x ^ s.re * ‖Complex.exp ((s + 1) * (Real.log (1 + δ) : ℂ)) - 1‖ /
    ‖(δ : ℂ) * s * (s + 1)‖ ≤ 4 * x / ‖s‖
  have hre : s.re = 1 := by simp [s]
  rw [hre, Real.rpow_one, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hδ]
  calc
    _ ≤ x * (δ * (4 * ‖s + 1‖)) / (δ * ‖s‖ * ‖s + 1‖) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hx.le) (by positivity)
    _ = _ := by field_simp [ne_of_gt hδ, ne_of_gt hs0, ne_of_gt hs10]


end TwoPointCorrelations

end OAI

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



theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]



theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring








theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]


lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl


theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply Real.log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]









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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem
namespace OAI

/-! Mertens' second theorem in bounded-error form.

The formal proof uses `Erdos970.Mertens.sum_prime_div_eq_log_log`.
Only the convention for the finite prime set differs from
`PrimeReciprocalInput`; zero contributes no prime to either convention.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma sievePrimesUpTo_eq_Ioc (x : ℝ) :
    sievePrimesUpTo x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [sievePrimesUpTo, mem_filter, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, hp⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hp, hprime⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeWindows
namespace OAI

/-! Prime logarithmic windows have bounded von Mangoldt mass at frequency
resolution `1/T`, once the primes are at least `T²`. This is the precise
short-interval sieve consequence used in the Halasz mean-square argument. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.BigOperators





/-- The same local mass bound for every window, with the lower cutoff imposed
on the prime set instead of on the window's left endpoint. -/
theorem halasz_prime_windows_above_square : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (T : ℝ) (P : Finset ℕ), B ≤ T →
      (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) → ∀ u : ℝ,
      (∑ p ∈ P.filter (fun (p : ℕ) =>
        u ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ u + 1 / T),
          Real.log (p : ℝ) / (p : ℝ)) ≤ C / T := by
  classical
  obtain ⟨C, B, hC, hB, hwindow⟩ := halasz_prime_log_window_bound
  refine ⟨C, B, hC, hB, ?_⟩
  intro T P hBT hP u
  have hT : 2 ≤ T := hB.trans hBT
  have hTp : 0 < T := by linarith
  have hi : 1 / T ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hT
  have hl := Real.one_sub_inv_le_log_of_pos hTp
  have hl1 : 1 ≤ 2 * Real.log T := by
    rw [← one_div] at hl
    linarith
  let v := max u (2 * Real.log T)
  have hv : 1 ≤ v := hl1.trans (le_max_right _ _)
  have hscale : T ^ 2 ≤ Real.exp v := by
    calc
      T ^ 2 = Real.exp (Real.log (T ^ 2)) := (Real.exp_log (sq_pos_of_pos hTp)).symm
      _ = Real.exp (2 * Real.log T) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.exp v := Real.exp_le_exp.mpr (le_max_right _ _)
  apply hwindow T v _ hBT hv hscale
  intro p hp
  obtain ⟨hpP, hlo, hhi⟩ := mem_filter.mp hp
  have hlog := Real.log_le_log (sq_pos_of_pos hTp) (hP p hpP).2
  rw [Real.log_pow] at hlog
  refine ⟨(hP p hpP).1, max_le hlo hlog, ?_⟩
  exact hhi.trans (add_le_add (le_max_left _ _) le_rfl)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMeanSquare
namespace OAI

/-! A prime-supported mean-value theorem with one von Mangoldt weight,
proved from the Brun--Titchmarsh theorem and the exact Fourier
kernel. This is the sparse mean-square input to Halasz's argument. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.BigOperators

/-- Arbitrary complex prime coefficients are permitted. The constant is
independent of the upper end of the finite prime set. -/
theorem halasz_prime_mean_square : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (T : ℝ) (P : Finset ℕ), B ≤ T →
      (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) → ∀ a : ℕ → ℂ,
      (∫ t in -T..T,
        ‖mrtExponentialPolynomial P
          (fun p => a p * ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ))
          (fun p => -Real.log (p : ℝ)) t‖ ^ 2) ≤
        C * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / (p : ℝ)) := by
  obtain ⟨C, B, hC, hB, hwindow⟩ := halasz_prime_windows_above_square
  refine ⟨Real.exp 1 * (16 * C), B, by positivity, hB, ?_⟩
  intro T P hBT hP a
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (hB.trans hBT)
  have hw : ∀ p ∈ P, 0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le))
      (Nat.cast_nonneg _)
  have hrow : ∀ p ∈ P,
      (∑ q ∈ P, (Real.log (q : ℝ) / (q : ℝ)) *
        (2 * T / (1 + T ^ 2 * (-Real.log (p : ℝ) - -Real.log (q : ℝ)) ^ 2))) ≤
          16 * C := by
    intro p hp
    have hh := halasz_frequency_row_of_windows P (fun q => Real.log (q : ℝ))
      (fun q => Real.log (q : ℝ) / (q : ℝ)) (Real.log (p : ℝ)) hT hC.le hw
      (hwindow T P hBT hP)
    convert (preTransparency := .instances) hh using 1
    apply sum_congr rfl
    intro q _
    rw [show (-Real.log (p : ℝ) - -Real.log (q : ℝ)) ^ 2 =
      (Real.log (q : ℝ) - Real.log (p : ℝ)) ^ 2 by ring]
  exact halasz_mean_square_of_weighted_rows P a
    (fun p => Real.log (p : ℝ) / (p : ℝ)) (fun p => -Real.log (p : ℝ)) hT hw hrow

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTranslatedMeanSquare
namespace OAI

/-! Translation of the prime mean square, including unit windows. The
translation only changes the phases of the arbitrary prime coefficients. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory

lemma halasz_polynomial_translate {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (u t : ℝ) :
    mrtExponentialPolynomial S
      (fun i => a i * Complex.exp (((freq i * u : ℝ) : ℂ) * Complex.I)) freq t =
      mrtExponentialPolynomial S a freq (t + u) := by
  unfold mrtExponentialPolynomial
  apply sum_congr rfl
  intro i _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma halasz_polynomial_continuous {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) : Continuous (mrtExponentialPolynomial S a freq) := by
  unfold mrtExponentialPolynomial
  fun_prop


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass
namespace OAI

/-! Mertens' first theorem, in the prime-band convention needed for the
small- and large-prime truncations in the Halasz convolution. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszMertensConstant_nonneg : 0 ≤ halaszMertensConstant := by
  unfold halaszMertensConstant
  positivity

lemma halasz_prime_prefix_mass {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) - Real.log x| ≤
      halaszMertensConstant := by
  rw [sievePrimesUpTo_eq_Ioc]
  exact Erdos970.Mertens.sum_log_prime_div_eq_log hx



lemma halasz_prime_prefix_mass_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) ≤
      Real.log x + halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_prefix_mass hx)).2]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitPrimeWindows
namespace OAI

/-! A fixed-width mean square for every finite prime set. The finitely many
primes below the sieve threshold cost only an absolute constant. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_prime_fixed_rows : ∃ R B : ℝ, 0 < R ∧ 2 ≤ B ∧
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ u : ℝ,
      (∑ p ∈ P, (Real.log (p : ℝ) / p) *
        (2 * B / (1 + B ^ 2 * (Real.log (p : ℝ) - u) ^ 2))) ≤ R := by
  obtain ⟨C, B, hC, hB, hwindow⟩ := halasz_prime_windows_above_square
  let M := Real.log (B ^ 2) + halaszMertensConstant
  have hBp : 0 < B := by linarith
  have hB2 : 1 ≤ B ^ 2 := by nlinarith
  have hM : 0 ≤ M := add_nonneg (Real.log_nonneg hB2) halaszMertensConstant_nonneg
  refine ⟨16 * C + 2 * B * M, B, by positivity, hB, ?_⟩
  intro P hP u
  let L := P.filter (fun p : ℕ => B ^ 2 ≤ (p : ℝ))
  let S := P \ L
  let w := fun p : ℕ => Real.log (p : ℝ) / p
  let K := fun p : ℕ => 2 * B / (1 + B ^ 2 * (Real.log (p : ℝ) - u) ^ 2)
  have hLP : L ⊆ P := filter_subset _ _
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ w p :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)
  have hlarge : ∑ p ∈ L, w p * K p ≤ 16 * C := by
    exact halasz_frequency_row_of_windows L (fun p => Real.log (p : ℝ)) w u hBp hC.le
      (fun p hp => hw p (hLP hp))
      (hwindow B L le_rfl (fun p hp => ⟨hP p (hLP hp), (mem_filter.mp hp).2⟩))
  have hsmall : ∑ p ∈ S, w p ≤ M := by
    have hsub : S ⊆ sievePrimesUpTo (B ^ 2) := by
      intro p hp
      obtain ⟨hpP, hpL⟩ := mem_sdiff.mp hp
      have hpB : (p : ℝ) < B ^ 2 := by
        by_contra! hn
        exact hpL (mem_filter.mpr ⟨hpP, hn⟩)
      exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (by positivity)).mpr hpB.le), hP p hpP⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast (sievePrimesUpTo_prime _ p hp).one_le))
        (Nat.cast_nonneg _))).trans (halasz_prime_prefix_mass_le hB2)
  have hK (p : ℕ) : K p ≤ 2 * B := by
    apply div_le_self (by positivity)
    nlinarith [mul_nonneg (sq_nonneg B) (sq_nonneg (Real.log (p : ℝ) - u))]
  have hsmallrow : ∑ p ∈ S, w p * K p ≤ 2 * B * M := by
    calc
      _ ≤ ∑ p ∈ S, w p * (2 * B) :=
        sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hK p) (hw p (mem_sdiff.mp hp).1))
      _ = 2 * B * ∑ p ∈ S, w p := by rw [← sum_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
  have he : (∑ p ∈ P, w p * K p) = (∑ p ∈ L, w p * K p) + ∑ p ∈ S, w p * K p := by
    dsimp [S]
    rw [sum_sdiff_eq_sub hLP]
    ring
  change (∑ p ∈ P, w p * K p) ≤ _
  rw [he]
  exact add_le_add hlarge hsmallrow

/-- The unit-interval prime mean square, with no lower prime cutoff. -/
theorem halasz_prime_mean_square_unit : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ (a : ℕ → ℂ) (u : ℝ),
      (∫ t in (u - 1 / 2)..(u + 1 / 2),
        ‖mrtExponentialPolynomial P
          (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
          (fun p => -Real.log (p : ℝ)) t‖ ^ 2) ≤
        C * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p) := by
  obtain ⟨R, B, hR, hB, hrows⟩ := halasz_prime_fixed_rows
  refine ⟨Real.exp 1 * R, by positivity, ?_⟩
  intro P hP a u
  let w := fun p : ℕ => Real.log (p : ℝ) / p
  let freq := fun p : ℕ => -Real.log (p : ℝ)
  let phase := fun p => Complex.exp (((freq p * u : ℝ) : ℂ) * Complex.I)
  let D := mrtExponentialPolynomial P (fun p => a p * (w p : ℂ)) freq
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ w p :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)
  have hr : ∀ p ∈ P,
      (∑ q ∈ P, w q * (2 * B / (1 + B ^ 2 * (freq p - freq q) ^ 2))) ≤ R := by
    intro p _
    convert (preTransparency := .instances) hrows P hP (Real.log (p : ℝ)) using 1
    apply sum_congr rfl
    intro q _
    dsimp [freq]
    ring
  have hm := halasz_mean_square_of_weighted_rows P (fun p => a p * phase p) w freq
    (by linarith : 0 < B) hw hr
  have he (t : ℝ) : mrtExponentialPolynomial P (fun p => (a p * phase p) * (w p : ℂ))
      freq t = D (t + u) := by
    dsimp only [D]
    rw [← halasz_polynomial_translate]
    unfold mrtExponentialPolynomial
    apply sum_congr rfl
    intro p _
    dsimp [phase]
    ring
  have hp (p : ℕ) : ‖a p * phase p‖ = ‖a p‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  simp_rw [he, hp] at hm
  have ht := intervalIntegral.integral_comp_add_right (fun t => ‖D t‖ ^ 2) u
    (a := -B) (b := B)
  rw [ht] at hm
  have hmono : (∫ t in (u - 1 / 2)..(u + 1 / 2), ‖D t‖ ^ 2) ≤
      ∫ t in (-B + u)..(B + u), ‖D t‖ ^ 2 := by
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun t => sq_nonneg _))
    exact ((halasz_polynomial_continuous P _ freq).norm.pow 2).intervalIntegrable _ _
  exact hmono.trans hm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCauchyMeanSquare
namespace OAI

/-! Summing the translated unit-window estimates against the Cauchy
weight gives the global weighted mean square used in the Perron argument. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_polynomial_norm_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    ‖mrtExponentialPolynomial S a freq t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  unfold mrtExponentialPolynomial
  exact (norm_sum_le _ _).trans (by
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl])

lemma halasz_cauchy_polynomial_integrable {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) :
    Integrable (fun t : ℝ => ‖mrtExponentialPolynomial S a freq t‖ ^ 2 * (1 + t ^ 2)⁻¹) := by
  have hc : Continuous (fun t : ℝ =>
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2 * (1 + t ^ 2)⁻¹) := by
    apply ((halasz_polynomial_continuous S a freq).norm.pow 2).mul
    exact (continuous_const.add (continuous_id.pow 2)).inv₀
      (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2))
  apply (integrable_inv_one_add_sq.const_mul ((∑ i ∈ S, ‖a i‖) ^ 2)).mono'
    hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (halasz_polynomial_norm_le S a freq t) 2)
    (by positivity)

lemma halasz_cauchy_integer_summable : Summable (fun k : ℤ => (1 + (k : ℝ) ^ 2)⁻¹) := by
  have hsingle : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [mem_singleton] at hk
    simp [hk]
  have hp := (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).add hsingle
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hp
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk, add_zero]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_ne_zero hk0)
      (show (k : ℝ) ^ 2 ≤ 1 + (k : ℝ) ^ 2 by linarith)

lemma halasz_cauchy_weight_window {k t : ℝ} (ht : t ∈ Set.Icc (k - 1 / 2) (k + 1 / 2)) :
    (1 + t ^ 2)⁻¹ ≤ 2 * (1 + k ^ 2)⁻¹ := by
  have hgap : (k - t) ^ 2 ≤ 1 / 4 := by
    have hp := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
    nlinarith
  have hden : 1 + k ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (2 * t - k)]
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hkpos : 0 < 1 + k ^ 2 := by positivity
  simpa only [div_eq_mul_inv, one_mul] using
    (div_le_div_iff₀ hpos hkpos).mpr (show (1 : ℝ) * (1 + k ^ 2) ≤ 2 * (1 + t ^ 2) by nlinarith)

theorem halasz_prime_mean_square_cauchy : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ a : ℕ → ℂ,
      (∫ t : ℝ, ‖mrtExponentialPolynomial P
        (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖ ^ 2 * (1 + t ^ 2)⁻¹) ≤
        C * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p) := by
  obtain ⟨C, hC, hm⟩ := halasz_prime_mean_square_unit
  let W := ∑' k : ℤ, (1 + (k : ℝ) ^ 2)⁻¹
  have hW : 0 ≤ W := tsum_nonneg (fun _ => by positivity)
  refine ⟨C * (1 + 2 * W), by positivity, ?_⟩
  intro P hP a
  let D := mrtExponentialPolynomial P
    (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ)) (fun p => -Real.log (p : ℝ))
  let M := ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)
  have hM : 0 ≤ M := sum_nonneg (fun p hp => mul_nonneg (sq_nonneg _)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)))
  have hi : Integrable (fun t : ℝ => ‖D t‖ ^ 2 * (1 + t ^ 2)⁻¹) :=
    halasz_cauchy_polynomial_integrable P _ _
  have hs := hi.hasSum_intervalIntegral (-(1 / 2 : ℝ))
  have hb (k : ℤ) : (∫ t in (-(1 / 2 : ℝ) + k)..(-(1 / 2 : ℝ) + k + 1),
      ‖D t‖ ^ 2 * (1 + t ^ 2)⁻¹) ≤ (2 * C * M) * (1 + (k : ℝ) ^ 2)⁻¹ := by
    have he1 : -(1 / 2 : ℝ) + k = (k : ℝ) - 1 / 2 := by ring
    have he2 : -(1 / 2 : ℝ) + k + 1 = (k : ℝ) + 1 / 2 := by ring
    rw [he2, he1]
    have hc := (halasz_polynomial_continuous P
      (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
      (fun p => -Real.log (p : ℝ))).norm.pow 2
    calc
      _ ≤ ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
          (2 * (1 + (k : ℝ) ^ 2)⁻¹) * ‖D t‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith) hi.intervalIntegrable
          ((hc.const_mul _).intervalIntegrable _ _)
        intro t ht
        simpa only [D, Pi.pow_apply, mul_comm] using mul_le_mul_of_nonneg_left
          (halasz_cauchy_weight_window ht) (sq_nonneg ‖D t‖)
      _ = (2 * (1 + (k : ℝ) ^ 2)⁻¹) *
          ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), ‖D t‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (2 * (1 + (k : ℝ) ^ 2)⁻¹) * (C * M) :=
        mul_le_mul_of_nonneg_left (hm P hP a k) (by positivity)
      _ = _ := by ring
  have hsum := hs.summable.tsum_le_tsum hb (halasz_cauchy_integer_summable.mul_left (2 * C * M))
  rw [hs.tsum_eq, tsum_mul_left] at hsum
  change _ ≤ _
  change _ ≤ C * (1 + 2 * W) * M
  change _ ≤ 2 * C * M * W at hsum
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCauchySchwarz
namespace OAI

/-! The finite-interval Cauchy--Schwarz step of the triple convolution.
One factor keeps its unweighted prime mean square; the second uses the
Cauchy weight from Perron's kernel. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_integral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t) :
    (∫ t in a..b, f t * g t) ≤
      Real.sqrt (∫ t in a..b, f t ^ 2) * Real.sqrt (∫ t in a..b, g t ^ 2) := by
  let μ := volume.restrict (Set.Ioc a b)
  have hfm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hgm : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hfs : Integrable (fun t => f t ^ 2) μ :=
    ((hf.pow 2).continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hgs : Integrable (fun t => g t ^ 2) μ :=
    ((hg.pow 2).continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hfl : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).mpr hfs
  have hgl : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm).mpr hgs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hfl) (by simpa using hgl)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  simpa only [intervalIntegral.integral_of_le hab, μ] using h

lemma halasz_weighted_integral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b)
    (P Q : ℝ → ℂ) (hP : Continuous P) (hQ : Continuous Q) :
    (∫ t in a..b, ‖P t‖ * ‖Q t‖ / Real.sqrt (1 + t ^ 2)) ≤
      Real.sqrt (∫ t in a..b, ‖P t‖ ^ 2) *
        Real.sqrt (∫ t in a..b, ‖Q t‖ ^ 2 * (1 + t ^ 2)⁻¹) := by
  have hg : Continuous (fun t => ‖Q t‖ / Real.sqrt (1 + t ^ 2)) := by
    exact hQ.norm.div ((continuous_const.add (continuous_id.pow 2)).sqrt)
      (fun t => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have h := halasz_integral_cauchy_schwarz hab (fun t => ‖P t‖)
    (fun t => ‖Q t‖ / Real.sqrt (1 + t ^ 2)) hP.norm hg (fun _ => norm_nonneg _)
    (fun _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have he (t : ℝ) : (‖Q t‖ / Real.sqrt (1 + t ^ 2)) ^ 2 =
      ‖Q t‖ ^ 2 * (1 + t ^ 2)⁻¹ := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    rfl
  simp_rw [he] at h
  simpa only [mul_div_assoc] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowIntegral
namespace OAI

/-! The central part of the prime--prime--smooth Perron integral.
The first prime factor uses its ordinary mean square and the second its
global Cauchy-weighted mean square. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset

lemma halasz_vertical_norm (t : ℝ) :
    ‖(1 : ℂ) + (t : ℂ) * I‖ = Real.sqrt (1 + t ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply, pow_two]

lemma halasz_window_middle_bound {x δ T A : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (P Q F : ℝ → ℂ) (hP : Continuous P) (hQ : Continuous Q)
    (hF : ∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ A) :
    ‖∫ t in -T..T, P t * Q t * F t *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)‖ ≤
      (4 * x * A) * (Real.sqrt (∫ t in -T..T, ‖P t‖ ^ 2) *
        Real.sqrt (∫ t in -T..T, ‖Q t‖ ^ 2 * (1 + t ^ 2)⁻¹)) := by
  let G := fun t : ℝ => ‖P t‖ * ‖Q t‖ / Real.sqrt (1 + t ^ 2)
  have hG : Continuous G := by
    exact (hP.norm.mul hQ.norm).div ((continuous_const.add (continuous_id.pow 2)).sqrt)
      (fun t => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖P t * Q t * F t * halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)‖ ≤
        (4 * x * A) * G t := by
    rw [norm_mul, norm_mul, norm_mul]
    have hk := halasz_perron_window_bound hx hδ hδ1 t
    rw [halasz_vertical_norm] at hk
    calc
      _ ≤ (‖P t‖ * ‖Q t‖ * A) * (4 * x / Real.sqrt (1 + t ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hF t ht) (by positivity)) hk
          (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [G]; ring
  calc
    _ ≤ ∫ t in -T..T, (4 * x * A) * G t := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Filter.Eventually.of_forall (fun t ht => hbound t ⟨ht.1.le, ht.2⟩))
        ((hG.const_mul _).intervalIntegrable _ _)
    _ = (4 * x * A) * ∫ t in -T..T, G t := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (halasz_weighted_integral_cauchy_schwarz (by linarith) P Q hP hQ) (by positivity)

theorem halasz_prime_window_middle_oai : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (x δ T A : ℝ), 0 < x → 0 < δ → δ ≤ 1 → B ≤ T → 0 ≤ A →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ (a b : ℕ → ℂ) (F : ℝ → ℂ),
      (∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ A) →
      ‖∫ t in -T..T,
        mrtExponentialPolynomial P (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
          (fun p => -Real.log (p : ℝ)) t *
        mrtExponentialPolynomial Q (fun q => b q * ((Real.log (q : ℝ) / q : ℝ) : ℂ))
          (fun q => -Real.log (q : ℝ)) t * F t *
        halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)‖ ≤
        (C * x * A) * (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) := by
  obtain ⟨C₁, B, hC₁, hB, hfirst⟩ := halasz_prime_mean_square
  obtain ⟨C₂, hC₂, hsecond⟩ := halasz_prime_mean_square_cauchy
  refine ⟨4 * Real.sqrt C₁ * Real.sqrt C₂, B, by positivity, hB, ?_⟩
  intro x δ T A hx hδ hδ1 hBT hA P Q hP hQ a b F hF
  have hT : 0 ≤ T := (by linarith : (0 : ℝ) ≤ B).trans hBT
  let P₁ := mrtExponentialPolynomial P
    (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ)) (fun p => -Real.log (p : ℝ))
  let Q₁ := mrtExponentialPolynomial Q
    (fun q => b q * ((Real.log (q : ℝ) / q : ℝ) : ℂ)) (fun q => -Real.log (q : ℝ))
  have hp : (∫ t in -T..T, ‖P₁ t‖ ^ 2) ≤
      C₁ * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p) := hfirst T P hBT hP a
  have hqi := halasz_cauchy_polynomial_integrable Q
    (fun q => b q * ((Real.log (q : ℝ) / q : ℝ) : ℂ)) (fun q => -Real.log (q : ℝ))
  have hq : (∫ t in -T..T, ‖Q₁ t‖ ^ 2 * (1 + t ^ 2)⁻¹) ≤
      C₂ * ∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q) := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    exact (setIntegral_le_integral hqi (Filter.Eventually.of_forall (fun t => by positivity))).trans
      (hsecond Q hQ b)
  have hmid := halasz_window_middle_bound hx hδ hδ1 hT hA P₁ Q₁ F
    (halasz_polynomial_continuous P _ _) (halasz_polynomial_continuous Q _ _) hF
  apply hmid.trans
  calc
    _ ≤ (4 * x * A) *
        (Real.sqrt (C₁ * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (C₂ * ∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hp) (Real.sqrt_le_sqrt hq)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by rw [Real.sqrt_mul hC₁.le, Real.sqrt_mul hC₂.le]; ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_prime_window_middle_oai := @OAI.TwoPointCorrelations.halasz_prime_window_middle_oai
