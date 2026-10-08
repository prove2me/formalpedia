-- Prove2me | solution 1 for OAI.TwoPointCorrelations.HalaszPrimeSparseInput.large_prime_product_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:22:14.625794+00:00
-- url     : https://prove2.me/submissions/bd554071-4dd9-43f9-be48-86538000fc1e

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

/-- The standard Dirichlet-polynomial mean-value bound, with an absolute
constant and no logarithmic loss.  Arbitrary complex coefficients are allowed. -/
theorem mrt_dirichlet_mean_square (N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial (Finset.Ioc 0 N) a (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + (N : ℝ)) * ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 := by
  have hrow : ∀ m ∈ Finset.Ioc 0 N,
      (∑ n ∈ Finset.Ioc 0 N, 2 * T /
        (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2)) ≤
          8 * (T + (N : ℝ)) := by
    intro m hm
    convert (preTransparency := .instances) mrt_logarithmic_kernel_row hT hm using 1
    apply sum_congr rfl
    intro n _
    congr 2
    ring
  calc
    _ ≤ Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial (Finset.Ioc 0 N) a (fun n => -Real.log (n : ℝ)) t‖ ^ 2 :=
      mrt_unweighted_mean_square_le _ _ _ hT
    _ ≤ Real.exp 1 * (8 * (T + (N : ℝ)) * ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2) :=
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeProducts
namespace OAI

/-! The factorial multiplicity of a product of primes.  Sorting gives
an injective permutation code on each product fiber, including tuples
with repeated primes.  This is the arithmetic input for high moments
of prime Dirichlet polynomials. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_prime_tuples_perm {r : ℕ} (v w : Fin r → ℕ)
    (hv : ∀ i, (v i).Prime) (hw : ∀ i, (w i).Prime)
    (hprod : (∏ i, v i) = ∏ i, w i) : List.Perm (List.ofFn v) (List.ofFn w) := by
  have hpv := Nat.primeFactorsList_unique (List.prod_ofFn (f := v)) (by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hv i)
  have hpw := Nat.primeFactorsList_unique (List.prod_ofFn (f := w)) (by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hw i)
  rw [hprod] at hpv
  exact hpv.trans hpw.symm

lemma mrt_prime_tuples_sorted_eq {r : ℕ} (v w : Fin r → ℕ)
    (hv : ∀ i, (v i).Prime) (hw : ∀ i, (w i).Prime)
    (hprod : (∏ i, v i) = ∏ i, w i) :
    v ∘ Tuple.sort v = w ∘ Tuple.sort w := by
  have hp := ((Tuple.sort v).ofFn_comp_perm v).trans
    ((mrt_prime_tuples_perm v w hv hw hprod).trans ((Tuple.sort w).ofFn_comp_perm w).symm)
  exact List.ofFn_injective (hp.eq_of_pairwise'
    (Tuple.monotone_sort v).sortedLE_ofFn.pairwise
    (Tuple.monotone_sort w).sortedLE_ofFn.pairwise)

theorem mrt_prime_product_fiber_card {r : ℕ} (S : Finset (Fin r → ℕ))
    (hS : ∀ v ∈ S, ∀ i, (v i).Prime) (n : ℕ) :
    (S.filter (fun v => (∏ i, v i) = n)).card ≤ r.factorial := by
  let T := S.filter (fun v => (∏ i, v i) = n)
  have hcard : T.card ≤ (univ : Finset (Equiv.Perm (Fin r))).card := by
    apply card_le_card_of_injOn Tuple.sort (fun _ _ => mem_univ _)
    intro v hv w hw he
    have hv' := mem_filter.mp hv
    have hw' := mem_filter.mp hw
    have hs := mrt_prime_tuples_sorted_eq v w (hS v hv'.1) (hS w hw'.1)
      (hv'.2.trans hw'.2.symm)
    funext i
    have hi := congrFun hs ((Tuple.sort v).symm i)
    rw [← he] at hi
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi
  simpa only [card_univ, Fintype.card_perm, Fintype.card_fin] using hcard

lemma mrt_norm_sum_sq_le_card {α : Type*} (S : Finset α) (a : α → ℂ) :
    ‖∑ i ∈ S, a i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ S, ‖a i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖a i‖)

/-- Equal products of `r` primes contribute at most the factorial loss
to the square of a grouped Dirichlet coefficient. -/
theorem mrt_prime_product_coefficient_sq {r : ℕ} (S : Finset (Fin r → ℕ))
    (hS : ∀ v ∈ S, ∀ i, (v i).Prime) (a : (Fin r → ℕ) → ℂ) (n : ℕ) :
    ‖∑ v ∈ S.filter (fun v => (∏ i, v i) = n), a v‖ ^ 2 ≤
      (r.factorial : ℝ) * ∑ v ∈ S.filter (fun v => (∏ i, v i) = n), ‖a v‖ ^ 2 := by
  apply (mrt_norm_sum_sq_le_card _ a).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  exact_mod_cast mrt_prime_product_fiber_card S hS n

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeMoments
namespace OAI

/-! High even moments of a prime Dirichlet polynomial.  Expanding the
power produces ordered prime tuples; unique factorization bounds each
coefficient fiber by the factorial, and the ordinary mean-square theorem
then applies to a polynomial of length `N ^ r`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical


lemma mrt_prime_tuple_range (P : Finset ℕ) (N r : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (v : Fin r → ℕ) (hv : v ∈ Fintype.piFinset fun _ : Fin r => P) :
    (∏ i, v i) ∈ Ioc 0 (N ^ r) := by
  have hm : ∀ i, v i ∈ P := Fintype.mem_piFinset.mp hv
  refine mem_Ioc.mpr ⟨prod_pos fun i _ => (hP _ (hm i)).pos, ?_⟩
  calc
    _ ≤ ∏ _i : Fin r, N := prod_le_prod' fun i _ => hN _ (hm i)
    _ = _ := by simp

theorem mrt_prime_power_coefficient_mass (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N) :
    (∑ n ∈ Ioc 0 (N ^ r), ‖mrtPrimePowerCoefficient P a r n‖ ^ 2) ≤
      (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
  let S := Fintype.piFinset fun _ : Fin r => P
  have hs : ∀ v ∈ S, ∀ i, (v i).Prime := by
    intro v hv i
    exact hP _ (Fintype.mem_piFinset.mp hv i)
  calc
    _ ≤ ∑ n ∈ Ioc 0 (N ^ r), (r.factorial : ℝ) *
        ∑ v ∈ S.filter (fun v => (∏ i, v i) = n), ‖∏ i, a (v i)‖ ^ 2 := by
      apply sum_le_sum
      intro n _
      exact mrt_prime_product_coefficient_sq S hs (fun v => ∏ i, a (v i)) n
    _ = (r.factorial : ℝ) * ∑ v ∈ S, ‖∏ i, a (v i)‖ ^ 2 := by
      rw [← mul_sum]
      congr 1
      exact sum_fiberwise_of_maps_to (fun v hv => mrt_prime_tuple_range P N r hP hN v hv) _
    _ = _ := by
      congr 1
      simp only [norm_prod, ← prod_pow]
      exact (sum_pow' P (fun p => ‖a p‖ ^ 2) r).symm

lemma mrt_prime_tuple_phase {r : ℕ} (v : Fin r → ℕ)
    (hv : ∀ i, 0 < v i) (t : ℝ) :
    (∏ i, Complex.exp (((-Real.log (v i : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((-Real.log ((∏ i, v i : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_sum]
  have hl : Real.log ((∏ i, v i : ℕ) : ℝ) = ∑ i, Real.log (v i : ℝ) := by
    push_cast
    exact Real.log_prod fun i _ => by exact_mod_cast (hv i).ne'
  rw [hl]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [← sum_mul, ← sum_mul, sum_neg_distrib]

theorem mrt_prime_polynomial_power (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N) (t : ℝ) :
    (mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t) ^ r =
      mrtExponentialPolynomial (Ioc 0 (N ^ r)) (mrtPrimePowerCoefficient P a r)
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtExponentialPolynomial
  rw [sum_pow']
  symm
  calc
    _ = ∑ n ∈ Ioc 0 (N ^ r), ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
        (fun v => (∏ i, v i) = n),
          (∏ i, a (v i)) * Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
      apply sum_congr rfl
      intro n _
      exact sum_mul _ _ _
    _ = ∑ v ∈ Fintype.piFinset fun _ : Fin r => P,
        (∏ i, a (v i)) *
          Complex.exp (((-Real.log ((∏ i, v i : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
      calc
        _ = ∑ n ∈ Ioc 0 (N ^ r), ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
            (fun v => (∏ i, v i) = n), (∏ i, a (v i)) *
              Complex.exp (((-Real.log ((∏ i, v i : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
          apply sum_congr rfl
          intro n _
          apply sum_congr rfl
          intro v hv
          rw [(mem_filter.mp hv).2]
        _ = _ := sum_fiberwise_of_maps_to
          (fun v hv => mrt_prime_tuple_range P N r hP hN v hv) _
    _ = _ := by
      apply sum_congr rfl
      intro v hv
      rw [prod_mul_distrib, mrt_prime_tuple_phase v
        (fun i => (hP _ (Fintype.mem_piFinset.mp hv i)).pos) t]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSampling
namespace OAI

/-! Sampling a differentiable function at separated points.  Unit
intervals give a finite Sobolev estimate, which will be applied to the
prime-polynomial powers already expanded into Dirichlet coefficients. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.RealInnerProductSpace

lemma mrt_value_le_unit_integral (F F' B : ℝ → ℝ)
    (hF : Continuous F) (hF' : ∀ t, HasDerivAt F (F' t) t)
    (hB : Continuous B) (hB0 : ∀ t, 0 ≤ B t)
    (hd : ∀ t, |F' t| ≤ B t) (a : ℝ) :
    F a ≤ ∫ t in a..(a + 1), F t + B t := by
  have hiB : IntervalIntegrable B volume a (a + 1) := hB.intervalIntegrable a (a + 1)
  have hp (y : ℝ) (hy : y ∈ Icc a (a + 1)) :
      F a ≤ F y + ∫ t in a..(a + 1), B t := by
    have hdiff : ‖F y - F a‖ ≤ ∫ t in a..y, B t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hy.1 hF.continuousOn
        (fun t _ => (hF' t).differentiableAt.differentiableWithinAt)
      · exact Filter.Eventually.of_forall fun t _ => by
          rw [(hF' t).deriv, Real.norm_eq_abs]
          exact hd t
      · exact hB.intervalIntegrable a y
    have hm : (∫ t in a..y, B t) ≤ ∫ t in a..(a + 1), B t :=
      intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
        (Filter.Eventually.of_forall hB0) hiB
    have he : F a - F y ≤ ‖F y - F a‖ := by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact le_abs_self _
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + 1)
    (continuous_const.intervalIntegrable a (a + 1))
    ((hF.add continuous_const).intervalIntegrable a (a + 1)) hp
  change (∫ t in a..(a + 1), F a) ≤
    ∫ t in a..(a + 1), F t + (∫ u in a..(a + 1), B u) at hi
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hF.intervalIntegrable a (a + 1))
    (continuous_const.intervalIntegrable a (a + 1)), intervalIntegral.integral_const] at hi
  have hlen : a + 1 - a = 1 := by ring
  simp only [hlen, one_smul] at hi
  rw [intervalIntegral.integral_add (hF.intervalIntegrable a (a + 1)) hiB]
  exact hi

lemma mrt_unit_intervals_disjoint (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    Set.Pairwise (S : Set ℝ) (fun x y => Disjoint (Set.Ioc x (x + 1))
      (Set.Ioc y (y + 1))) := by
  intro x hx y hy hne
  have h := hsep x hx y hy hne
  by_cases hxy : x ≤ y
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    exact Ioc_disjoint_Ioc_of_le (by linarith)
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))] at h
    exact (Ioc_disjoint_Ioc_of_le (by linarith : y + 1 ≤ x)).symm

lemma mrt_sum_unit_integrals_le (S : Finset ℝ) (G : ℝ → ℝ)
    (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ x ∈ S, a ≤ x ∧ x + 1 ≤ b) :
    (∑ x ∈ S, ∫ t in x..(x + 1), G t) ≤ ∫ t in a..b, G t := by
  have hint (x : ℝ) : (∫ t in x..(x + 1), G t) = ∫ t in Ioc x (x + 1), G t :=
    intervalIntegral.integral_of_le (by linarith)
  simp_rw [hint]
  rw [← integral_biUnion_finset S (fun _ _ => measurableSet_Ioc)
    (mrt_unit_intervals_disjoint S hsep)
    (fun x _ => (hG.intervalIntegrable x (x + 1)).1),
    intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set (hG.intervalIntegrable a b).1
    (Filter.Eventually.of_forall hG0)
  exact Filter.Eventually.of_forall fun t ht => by
    obtain ⟨x, hx, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨lt_of_le_of_lt (hS x hx).1 ht.1, ht.2.trans (hS x hx).2⟩

/-- A finite separated sample is controlled by the ordinary square
integrals of a function and its derivative. -/
theorem mrt_separated_square_samples (S : Finset ℝ) (q q' : ℝ → ℂ)
    (hq : Continuous q) (hq' : Continuous q')
    (hd : ∀ t, HasDerivAt q (q' t) t)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (a b : ℝ) (hab : a ≤ b) (hS : ∀ x ∈ S, a ≤ x ∧ x + 1 ≤ b) :
    (∑ x ∈ S, ‖q x‖ ^ 2) ≤ ∫ t in a..b, 2 * ‖q t‖ ^ 2 + ‖q' t‖ ^ 2 := by
  let F := fun t => ‖q t‖ ^ 2
  let B := fun t => ‖q t‖ ^ 2 + ‖q' t‖ ^ 2
  have hB : Continuous B := (hq.norm.pow 2).add (hq'.norm.pow 2)
  have hder (t : ℝ) : |2 * inner ℝ (q t) (q' t)| ≤ B t := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hi := abs_real_inner_le_norm (q t) (q' t)
    dsimp only [B]
    nlinarith [sq_nonneg (‖q t‖ - ‖q' t‖)]
  calc
    _ ≤ ∑ x ∈ S, ∫ t in x..(x + 1), F t + B t := by
      apply sum_le_sum
      intro x _
      exact mrt_value_le_unit_integral F (fun t => 2 * inner ℝ (q t) (q' t)) B
        (hq.norm.pow 2) (fun t => (hd t).norm_sq) hB
        (fun t => by dsimp only [B]; positivity) hder x
    _ ≤ ∫ t in a..b, F t + B t :=
      mrt_sum_unit_integrals_le S (fun t => F t + B t) ((hq.norm.pow 2).add hB)
        (fun t => by dsimp only [F, B]; positivity)
        hsep a b hab hS
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [F, B]
      ring

lemma mrt_exponential_polynomial_deriv {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    HasDerivAt (mrtExponentialPolynomial S a freq)
      (mrtExponentialPolynomial S (fun i => a i * ((freq i : ℂ) * Complex.I)) freq t) t := by
  unfold mrtExponentialPolynomial
  apply HasDerivAt.fun_sum
  intro i _
  have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (freq i : ℂ)).mul_const
    Complex.I).cexp.const_mul (a i)
  convert (preTransparency := .instances) h using 1
  · funext y
    simp only [Complex.ofReal_mul, Complex.ofRealCLM_apply]
  · simp only [Complex.ofReal_mul, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
    ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLargeValues
namespace OAI

/-! Large values at one-separated heights, obtained from the exact
prime-product expansion and the finite sampling inequality. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_dirichlet_derivative_mass (N : ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ Ioc 0 N, ‖a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I)‖ ^ 2) ≤
      (Real.log (N : ℝ)) ^ 2 * ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hn0 : 0 < n := (mem_Ioc.mp hn).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp hn).2
  have hlog0 := Real.log_nonneg hn1
  have hlogN := Real.log_le_log (by positivity : (0 : ℝ) < n) hnN
  simp only [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog0, mul_pow]
  calc
    _ ≤ ‖a n‖ ^ 2 * (Real.log (N : ℝ)) ^ 2 := by gcongr
    _ = _ := mul_comm _ _

theorem mrt_dirichlet_separated_samples (N : ℕ) (a : ℕ → ℂ)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial (Ioc 0 N) a
      (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + 1 + N) * (2 + (Real.log (N : ℝ)) ^ 2) *
        ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2 := by
  let q := mrtExponentialPolynomial (Ioc 0 N) a (fun n => -Real.log (n : ℝ))
  let q' := mrtExponentialPolynomial (Ioc 0 N)
    (fun n => a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I))
    (fun n => -Real.log (n : ℝ))
  have hq := mrtExponentialPolynomial_continuous (Ioc 0 N) a
    (fun n => -Real.log (n : ℝ))
  have hq' := mrtExponentialPolynomial_continuous (Ioc 0 N)
    (fun n => a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I))
    (fun n => -Real.log (n : ℝ))
  have hder (t : ℝ) : HasDerivAt q (q' t) t := by
    simpa only [q, q', Complex.ofReal_neg] using
      mrt_exponential_polynomial_deriv (Ioc 0 N) a (fun n => -Real.log (n : ℝ)) t
  have hs := mrt_separated_square_samples S q q' hq hq' hder hsep (-(T + 1)) (T + 1)
    (by linarith) (fun t ht => by
      have hh := abs_le.mp (hS t ht)
      constructor <;> linarith)
  have hm := mrt_dirichlet_mean_square N a (show 0 < T + 1 by linarith)
  have hm' := mrt_dirichlet_mean_square N
    (fun n => a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I))
    (show 0 < T + 1 by linarith)
  have hd := mrt_dirichlet_derivative_mass N a
  have hp : 0 ≤ 8 * Real.exp 1 * (T + 1 + N) := by positivity
  calc
    _ ≤ ∫ t in -(T + 1)..(T + 1), 2 * ‖q t‖ ^ 2 + ‖q' t‖ ^ 2 := hs
    _ = 2 * (∫ t in -(T + 1)..(T + 1), ‖q t‖ ^ 2) +
        ∫ t in -(T + 1)..(T + 1), ‖q' t‖ ^ 2 := by
      have hiq : IntervalIntegrable (fun t => 2 * ‖q t‖ ^ 2) volume (-(T + 1)) (T + 1) :=
        (continuous_const.mul (hq.norm.pow 2)).intervalIntegrable _ _
      have hiq' : IntervalIntegrable (fun t => ‖q' t‖ ^ 2) volume (-(T + 1)) (T + 1) :=
        (hq'.norm.pow 2).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hiq hiq', intervalIntegral.integral_const_mul]
    _ ≤ 2 * (8 * Real.exp 1 * (T + 1 + N) * ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2) +
        8 * Real.exp 1 * (T + 1 + N) *
          ((Real.log (N : ℝ)) ^ 2 * ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num))
        (hm'.trans (mul_le_mul_of_nonneg_left hd hp))
    _ = _ := by ring

/-- The sampled `2r`-th moment of an actual prime Dirichlet polynomial.
The extra logarithmic square comes only from sampling the continuous
moment on unit intervals. -/
theorem mrt_prime_separated_moment (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t‖ ^
      (2 * r)) ≤
      8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2) *
        (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
  have he (t : ℝ) : ‖mrtExponentialPolynomial P a
      (fun p => -Real.log (p : ℝ)) t‖ ^ (2 * r) =
      ‖mrtExponentialPolynomial (Ioc 0 (N ^ r)) (mrtPrimePowerCoefficient P a r)
        (fun n => -Real.log (n : ℝ)) t‖ ^ 2 := by
    rw [← mrt_prime_polynomial_power P a N r hP hN t, norm_pow, ← pow_mul]
    rw [Nat.mul_comm]
  simp_rw [he]
  apply (mrt_dirichlet_separated_samples (N ^ r) (mrtPrimePowerCoefficient P a r)
    S hT hS hsep).trans
  calc
    _ ≤ (8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2)) *
        ((r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r) := by
      apply mul_le_mul_of_nonneg_left (mrt_prime_power_coefficient_mass P a N r hP hN)
      positivity
    _ = _ := by ring

/-- A cardinality bound for one-separated large values. -/
theorem mrt_prime_large_values (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hlarge : ∀ t ∈ S,
      V ≤ ‖mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t‖) :
    (S.card : ℝ) ≤
      (8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2) *
        (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r) / V ^ (2 * r) := by
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  calc
    _ = ∑ _t ∈ S, V ^ (2 * r) := by simp
    _ ≤ ∑ t ∈ S, ‖mrtExponentialPolynomial P a
        (fun p => -Real.log (p : ℝ)) t‖ ^ (2 * r) := by
      apply sum_le_sum
      intro t ht
      exact pow_le_pow_left₀ hV.le (hlarge t ht) _
    _ ≤ _ := mrt_prime_separated_moment P a N r hP hN S hT hS hsep


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeSparseGram
namespace OAI

/-! The prime-supported sparse mean square keeps the reciprocal logarithmic
weight of the coefficient norm. The Mangoldt kernel estimate is an explicit
local hypothesis; its analytic proof is separate from this finite duality. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical



/-- The coefficient mass in a short logarithmic prime interval has both
logarithmic savings needed by the prime-supported sparse estimate. -/
theorem mrt_short_prime_logarithmic_mass : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (H u : ℝ) (P : Finset ℕ) (F : ℕ → ℂ), B ≤ H → 1 ≤ u →
      H^2 ≤ Real.exp u →
      (∀ p ∈ P, p.Prime ∧ u ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ u+1/H) →
      OneBounded F →
      (∑ p ∈ P, ‖F p/(p:ℂ)‖^2/Real.log (p:ℝ)) ≤
        C/(H*Real.exp u*u^2) := by
  obtain ⟨C,B,hC,hB,hwindow⟩ := halasz_prime_log_window_bound
  refine ⟨C,B,hC,hB,?_⟩
  intro H u P F hBH hu hscale hP hF
  have hH : 0 < H := lt_of_lt_of_le (by norm_num) (hB.trans hBH)
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hmass := hwindow H u P hBH hu hscale hP
  calc
    _ ≤ ∑ p ∈ P, (1/(Real.exp u*u^2))*(Real.log (p:ℝ)/(p:ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hp0 : (0:ℝ) < p := by exact_mod_cast (hP p hp).1.pos
      have hl : 0 < Real.log (p:ℝ) := hu0.trans_le (hP p hp).2.1
      have hey : Real.exp u ≤ (p:ℝ) := by
        simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr (hP p hp).2.1
      have hn : ‖F p/(p:ℂ)‖ ≤ 1/(p:ℝ) := by
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_right (hF p (hP p hp).1.pos) hp0.le
      have hd : Real.exp u*u^2 ≤ (p:ℝ)*(Real.log (p:ℝ))^2 := by
        exact mul_le_mul hey (pow_le_pow_left₀ hu0.le (hP p hp).2.1 2)
          (sq_nonneg _) hp0.le
      calc
        _ ≤ (1/(p:ℝ))^2/Real.log (p:ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) hl.le
        _ = (1/((p:ℝ)*(Real.log (p:ℝ))^2))*(Real.log (p:ℝ)/(p:ℝ)) := by
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (one_div_le_one_div_of_le (by positivity) hd) (by positivity)
    _ = (1/(Real.exp u*u^2))*∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ (1/(Real.exp u*u^2))*(C/H) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPublishedPrime
namespace OAI

/-! The precise published prime-supported sparse estimate needed for the
extra-prime argument. `HalaszPrimeSparseInput` specializes Matomäki--Radziwiłł,
*Multiplicative functions in short intervals*, Annals 183 (2016), Lemma 11
(arXiv:1501.04585v4), to T=exp L and epsilon=1/12. Replacing log Y by log p
costs at most an absolute factor on [Y,2Y]. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset


lemma halasz_sparse_prime_error :
    ∀ᶠ L : ℝ in atTop, ∀ Y R : ℝ,
      L^(79/80:ℝ) ≤ Real.log Y → 0 ≤ R → R ≤ Real.exp (L^(3/100:ℝ)) →
      R*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2 ≤ 1 := by
  have hlog := (isLittleO_log_rpow_atTop (show (0:ℝ)<19/80 by norm_num)).bound
    (show (0:ℝ)<1/4 by norm_num)
  have hpow := (tendsto_rpow_atTop (show (0:ℝ)<83/400 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hlog,hpow,eventually_ge_atTop (1:ℝ)] with L hlog hpow hL
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs,abs_of_nonneg hlog0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlog
  have hprod : L^(3/100:ℝ)*L^(83/400:ℝ)=L^(19/80:ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hsmall : 2*L^(3/100:ℝ) ≤ L^(19/80:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hL0.le (3/100))
    rw [hprod] at hh
    linarith
  intro Y R hY _hR hRbound
  have hquot : L^(79/80:ℝ)/L^(3/4:ℝ)=L^(19/80:ℝ) := by
    rw [← Real.rpow_sub hL0]
    norm_num
  have hlarge : L^(19/80:ℝ) ≤ Real.log Y/L^(3/4:ℝ) := by
    rw [← hquot]
    exact div_le_div_of_nonneg_right hY (Real.rpow_nonneg hL0.le _)
  have hsq : L^2=Real.exp (2*Real.log L) := by
    rw [show 2*Real.log L=Real.log L+Real.log L by ring,Real.exp_add,Real.exp_log hL0]
    ring
  calc
    _ ≤ Real.exp (L^(3/100:ℝ))*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2 := by
      gcongr
    _ = Real.exp (L^(3/100:ℝ)-Real.log Y/L^(3/4:ℝ)+2*Real.log L) := by
      rw [hsq,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem HalaszPrimeSparseInput.short_prime_energy (hprime : HalaszPrimeSparseInput) :
    ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧ ∀ᶠ L : ℝ in atTop,
      ∀ H Y : ℝ, B ≤ H → 2 ≤ Y → H^2 ≤ Y →
      L^(79/80:ℝ) ≤ Real.log Y → 1 ≤ Real.log Y →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
      (∀ p ∈ P, Real.log Y ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ Real.log Y+1/H) →
      OneBounded F → ∀ (S : Finset ℝ),
      (∀ t ∈ S, |t| ≤ Real.exp L) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (S.card:ℝ) ≤ Real.exp (L^(3/100:ℝ)) →
      (∑ t ∈ S, ‖mrtExponentialPolynomial P (fun p => F p/(p:ℂ))
        (fun p => -Real.log (p:ℝ)) t‖^2) ≤ C/(H*(Real.log Y)^2) := by
  obtain ⟨C₁,L₀,hC₁,hprime⟩ := hprime
  obtain ⟨C₂,B,hC₂,hB,hmass⟩ := mrt_short_prime_logarithmic_mass
  refine ⟨2*C₁*C₂,B,by positivity,hB,?_⟩
  filter_upwards [halasz_sparse_prime_error,eventually_ge_atTop L₀,
    eventually_ge_atTop (1:ℝ)] with L herror hL₀ hL
  intro H Y hH hY hHY hYL hlogY P F hP hwindow hF S hheight hsep hcard
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hlogY0 : 0 < Real.log Y := by linarith
  have he := herror Y S.card hYL (Nat.cast_nonneg _) hcard
  have hkernel := hprime L Y hL₀ hL hY P hP (fun p => F p/(p:ℂ)) S hheight hsep
  have hpref : Y+(S.card:ℝ)*Y*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2 ≤ 2*Y := by
    have hh := mul_le_mul_of_nonneg_left he hY0.le
    nlinarith
  have hm := hmass H (Real.log Y) P F hH hlogY
    (by simpa only [Real.exp_log hY0] using hHY)
    (fun p hp => ⟨(hP p hp).1,(hwindow p hp).1,(hwindow p hp).2⟩) hF
  rw [Real.exp_log hY0] at hm
  calc
    _ ≤ C₁*(2*Y)*(∑ p ∈ P, ‖F p/(p:ℂ)‖^2/Real.log (p:ℝ)) :=
      hkernel.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpref hC₁.le)
        (sum_nonneg (fun p hp => div_nonneg (sq_nonneg _)
          (by have hh := (hwindow p hp).1; linarith))))
    _ ≤ C₁*(2*Y)*(C₂/(H*Y*(Real.log Y)^2)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by field_simp [hH0.ne',hY0.ne',hlogY0.ne']

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAmplificationPower
namespace OAI

/-! The explicit amplification order used between two successive MRT
prime scales. The integer ceiling satisfies the exact support inequalities
needed by the mixed cofactor moment. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrt_nat_pow_eq_exp {Y : ℝ} (hY : 0 < Y) (r : ℕ) :
    Y ^ r = Real.exp ((r : ℝ) * Real.log Y) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hY]
  congr 1
  ring

theorem mrt_amplification_order_bounds {Y u : ℝ} (hY : 1 < Y) (hu : 1 ≤ u) :
    u ≤ Y ^ mrtAmplificationOrder Y u ∧
      Y ^ mrtAmplificationOrder Y u ≤ u * Y ∧
      (mrtAmplificationOrder Y u : ℝ) < Real.log u / Real.log Y + 1 := by
  have hY0 : 0 < Y := by linarith
  have hu0 : 0 < u := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hquot : 0 ≤ Real.log u / Real.log Y :=
    div_nonneg (Real.log_nonneg hu) hlogY.le
  have hlo : Real.log u / Real.log Y ≤ (mrtAmplificationOrder Y u : ℝ) :=
    Nat.le_ceil _
  have hhi : (mrtAmplificationOrder Y u : ℝ) < Real.log u / Real.log Y + 1 :=
    Nat.ceil_lt_add_one hquot
  refine ⟨?_, ?_, hhi⟩
  · calc
      u = Real.exp (Real.log u) := (Real.exp_log hu0).symm
      _ ≤ Real.exp ((mrtAmplificationOrder Y u : ℝ) * Real.log Y) :=
        Real.exp_le_exp.mpr ((div_le_iff₀ hlogY).mp hlo)
      _ = _ := (mrt_nat_pow_eq_exp hY0 _).symm
  · have hh : (mrtAmplificationOrder Y u : ℝ) * Real.log Y <
        Real.log u + Real.log Y := by
      have hh := (mul_lt_mul_of_pos_right hhi hlogY)
      rw [add_mul, div_mul_cancel₀ _ hlogY.ne', one_mul] at hh
      exact hh
    calc
      _ = Real.exp ((mrtAmplificationOrder Y u : ℝ) * Real.log Y) :=
        mrt_nat_pow_eq_exp hY0 _
      _ ≤ Real.exp (Real.log u + Real.log Y) := Real.exp_le_exp.mpr hh.le
      _ = u * Y := by rw [Real.exp_add, Real.exp_log hu0, Real.exp_log hY0]


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




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallSamples
namespace OAI

/-! The actual last-band witness controls the number of one-separated
samples in the no-small class. The moment order is left free for optimization. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical


theorem mrt_short_prime_large_samples (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {Y V T : ℝ} (hY : 1 < Y)
    (hbin : ∀ p ∈ P, Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y)
    (F : ℕ → ℂ) (hF : OneBounded F) (r : ℕ) (hT : 0 ≤ T) (hV : 0 < V)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t ≠ s → 1 ≤ |t-s|)
    (hlarge : ∀ t ∈ S, V ≤ ‖mrtExponentialPolynomial P
      (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖) :
    (S.card:ℝ) ≤ mrtShortPrimeSampleCost Y V T r := by
  have hcap (p : ℕ) (hp : p ∈ P) : p ≤ 2*⌈Y⌉₊ := by
    have hh := (hbin p hp).2.trans
      (mul_le_mul_of_nonneg_left (Nat.le_ceil Y) (by norm_num : (0:ℝ) ≤ 2))
    exact_mod_cast hh
  have hmass : (∑ p ∈ P, ‖F p/(p:ℂ)‖^2) ≤ 2/Y := by
    calc
      _ ≤ ∑ p ∈ P, 1/(p:ℝ)^2 := by
        apply sum_le_sum
        intro p hp
        rw [norm_div, Complex.norm_natCast, div_pow]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact (pow_le_pow_left₀ (norm_nonneg _) (hF p (hprime p hp).pos) 2).trans_eq
          (by norm_num)
      _ ≤ _ := mrt_finite_reciprocal_square_tail P hY.le (fun p hp => (hbin p hp).1)
  apply (mrt_prime_large_values P (fun p => F p/(p:ℂ)) (2*⌈Y⌉₊) r
    hprime hcap S hT hV hS hsep hlarge).trans
  unfold mrtShortPrimeSampleCost
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sum_nonneg (fun _ _ => sq_nonneg _)) hmass r) (by positivity)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSampleCost
namespace OAI

/-! Optimizing the actual finite sample moment at the first power reaching
the frequency height. The estimates apply to the last-band and additional
large-prime witnesses without replacing their literal sample cost. -/

namespace TwoPointCorrelations

/-- Once Y^r reaches the height, all ambient-height and rounding factors
are absorbed into an explicit exponential in the moment order. -/
theorem mrt_short_prime_sample_cost_le {Y V T : ℝ} (hY : 1 ≤ Y)
    (hV : 0 < V) {r : ℕ} (hTr : T ≤ Y^r) :
    mrtShortPrimeSampleCost Y V T r ≤
      24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2)*(8*(r:ℝ))^r/V^(2*r) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hc : Y ≤ (⌈Y⌉₊:ℝ) := Nat.le_ceil Y
  have hc' := Nat.ceil_lt_add_one hY0.le
  have hn1 : (1:ℝ) ≤ ((2*⌈Y⌉₊:ℕ):ℝ) := by push_cast; linarith
  have hn0 : (0:ℝ) < ((2*⌈Y⌉₊:ℕ):ℝ) := by linarith
  have hnle : ((2*⌈Y⌉₊:ℕ):ℝ) ≤ 4*Y := by push_cast; linarith
  have hnpr : (((2*⌈Y⌉₊)^r:ℕ):ℝ) ≤ (4*Y)^r := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ hn0.le hnle r
  have ht' : T ≤ (4*Y)^r := hTr.trans
    (pow_le_pow_left₀ hY0.le (by linarith) r)
  have hpow1 : (1:ℝ) ≤ (4*Y)^r := one_le_pow₀ (by linarith)
  have htime : T+1+(((2*⌈Y⌉₊)^r:ℕ):ℝ) ≤ 3*(4*Y)^r := by linarith
  have hlog : Real.log (((2*⌈Y⌉₊)^r:ℕ):ℝ) ≤ (r:ℝ)*Real.log (4*Y) := by
    rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hn0 hnle) (Nat.cast_nonneg _)
  have hlog0 : 0 ≤ Real.log (((2*⌈Y⌉₊)^r:ℕ):ℝ) := by
    apply Real.log_nonneg
    simpa only [Nat.cast_pow] using one_le_pow₀ hn1 (n := r)
  have hlog2 : 2+(Real.log (((2*⌈Y⌉₊)^r:ℕ):ℝ))^2 ≤
      2+((r:ℝ)*Real.log (4*Y))^2 := by
    have hh := pow_le_pow_left₀ hlog0 hlog 2
    linarith
  have hfac : (r.factorial:ℝ) ≤ (r:ℝ)^r := by exact_mod_cast Nat.factorial_le_pow r
  have hb : (4*Y)^r*(r:ℝ)^r*(2/Y)^r = (8*(r:ℝ))^r := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    field_simp
    ring
  unfold mrtShortPrimeSampleCost
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := mul_le_mul_of_nonneg_left htime (show 0 ≤ 8*Real.exp 1 by positivity)
  have h2 := mul_le_mul h1 hlog2 (by positivity) (by positivity)
  have h3 := mul_le_mul h2 hfac (by positivity) (by positivity)
  calc
    _ ≤ (8*Real.exp 1*(3*(4*Y)^r)*(2+((r:ℝ)*Real.log (4*Y))^2)*
        (r:ℝ)^r)*(2/Y)^r := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2)*
        ((4*Y)^r*(r:ℝ)^r*(2/Y)^r) := by ring
    _ = _ := by rw [hb]

/-- The exact ceiling moment realizes the preceding height balance. -/
theorem mrt_short_prime_sample_cost_chosen {Y V T : ℝ} (hY : 1 < Y)
    (hV : 0 < V) (hT : 1 ≤ T) :
    mrtShortPrimeSampleCost Y V T (mrtAmplificationOrder Y T) ≤
      24*Real.exp 1*
        (2+((mrtAmplificationOrder Y T:ℝ)*Real.log (4*Y))^2)*
        (8*(mrtAmplificationOrder Y T:ℝ))^(mrtAmplificationOrder Y T)/
        V^(2*mrtAmplificationOrder Y T) :=
  mrt_short_prime_sample_cost_le hY.le hV (mrt_amplification_order_bounds hY hT).1

/-- An exponential form suitable for the small fixed extra-band exponent. -/
theorem mrt_short_prime_sample_cost_exp {Y V T : ℝ} (hY : 1 < Y)
    (hV : 0 < V) (hT : 1 < T) :
    mrtShortPrimeSampleCost Y V T (mrtAmplificationOrder Y T) ≤
      24*Real.exp 1*
        (2+((mrtAmplificationOrder Y T:ℝ)*Real.log (4*Y))^2)*
        Real.exp ((mrtAmplificationOrder Y T:ℝ)*
          (Real.log (8*(mrtAmplificationOrder Y T:ℝ))-2*Real.log V)) := by
  let r := mrtAmplificationOrder Y T
  have hr : 0 < r := by
    dsimp [r, mrtAmplificationOrder]
    exact Nat.ceil_pos.mpr (div_pos (Real.log_pos hT) (Real.log_pos hY))
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have he : (8*(r:ℝ))^r/V^(2*r) =
      Real.exp ((r:ℝ)*(Real.log (8*(r:ℝ))-2*Real.log V)) := by
    rw [mrt_nat_pow_eq_exp (by positivity), mrt_nat_pow_eq_exp hV, ← Real.exp_sub]
    congr 1
    push_cast
    ring
  have hh := mrt_short_prime_sample_cost_chosen hY hV hT.le
  change mrtShortPrimeSampleCost Y V T r ≤ _ at hh ⊢
  calc
    _ ≤ (24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2))*
        ((8*(r:ℝ))^r/V^(2*r)) := by simpa only [mul_div_assoc] using hh
    _ = _ := by rw [he]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraSampleScale
namespace OAI

/-! The large-value sample count for the additional prime interval.
The lower-endpoint complement 1/80 is deliberately smaller than the published proof's
optimized choice; it preserves the exact MRT input rates. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma mrt_extra_sample_cost_pointwise {L Y T : ℝ}
    (hL : 4 ≤ L) (hLL : 1 ≤ Real.log L)
    (hsmall : (|Real.log (432*Real.exp 1)|+436)*Real.log L ≤ L^(7/(400:ℝ)))
    (hY : 1 < Y) (hYL : L^(79/(80:ℝ)) ≤ Real.log Y)
    (hYU : Real.log Y ≤ L) (hT : 1 < T) (hTU : T ≤ Real.exp L) :
    mrtShortPrimeSampleCost Y (L^(-100:ℝ)) T (mrtAmplificationOrder Y T) ≤
      Real.exp (L^(3/(100:ℝ))) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hV : 0 < L^(-100:ℝ) := Real.rpow_pos_of_pos hL0 _
  let r := mrtAmplificationOrder Y T
  have hrpos : 0 < r := by
    dsimp [r,mrtAmplificationOrder]
    exact Nat.ceil_pos.mpr (div_pos (Real.log_pos hT) (Real.log_pos hY))
  have hr0 : (0:ℝ) < r := by exact_mod_cast hrpos
  have hlogT : Real.log T ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log (by linarith : 0 < T) hTU
  have hpow1 : 1 ≤ L^(1/(80:ℝ)) := Real.one_le_rpow hL1 (by norm_num)
  have hpowL : L^(1/(80:ℝ)) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show (1/(80:ℝ)) ≤ 1 by norm_num)
  have hratio : L/L^(79/(80:ℝ)) = L^(1/(80:ℝ)) := by
    apply (div_eq_iff (Real.rpow_pos_of_pos hL0 _).ne').mpr
    rw [← Real.rpow_add hL0]
    norm_num
  have hr : (r:ℝ) ≤ 2*L^(1/(80:ℝ)) := by
    have hceil := (mrt_amplification_order_bounds hY hT.le).2.2.le
    change (r:ℝ) ≤ _ at hceil
    calc
      _ ≤ Real.log T/Real.log Y+1 := hceil
      _ ≤ L/L^(79/(80:ℝ))+1 := by
        have hd := (div_le_div_of_nonneg_right hlogT (Real.log_pos hY).le).trans
          (div_le_div_of_nonneg_left hL0.le (Real.rpow_pos_of_pos hL0 _) hYL)
        linarith
      _ ≤ _ := by rw [hratio]; linarith
  have hrL : (r:ℝ) ≤ 2*L := hr.trans (mul_le_mul_of_nonneg_left hpowL (by norm_num))
  have hlog4 : Real.log (4*Y) ≤ 2*L := by
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by linarith : Y ≠ 0)]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    linarith
  have hrl : 0 ≤ (r:ℝ)*Real.log (4*Y) :=
    mul_nonneg hr0.le (Real.log_nonneg (by linarith))
  have hrlb : (r:ℝ)*Real.log (4*Y) ≤ 4*L^2 := by
    calc
      _ ≤ (2*L)*(2*L) := mul_le_mul hrL hlog4 (Real.log_nonneg (by linarith)) (by positivity)
      _ = _ := by ring
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL1
  have hpref : 24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2) ≤
      432*Real.exp 1*L^4 := by
    have hs := pow_le_pow_left₀ hrl hrlb 2
    have he : (4*L^2)^2 = 16*L^4 := by ring
    rw [he] at hs
    have ht : 2+((r:ℝ)*Real.log (4*Y))^2 ≤ 18*L^4 := by nlinarith
    calc
      _ ≤ 24*Real.exp 1*(18*L^4) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have hlr : Real.log (8*(r:ℝ)) ≤ 16*Real.log L := by
    have hh := Real.log_le_log (by positivity : 0 < 8*(r:ℝ))
      (mul_le_mul_of_nonneg_left hrL (by norm_num : (0:ℝ) ≤ 8))
    have he : (8:ℝ)*(2*L)=16*L := by ring
    rw [he,Real.log_mul (by norm_num : (16:ℝ) ≠ 0) hL0.ne'] at hh
    have h16 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)
    linarith
  have hlogV : Real.log (L^(-100:ℝ)) = -100*Real.log L := by
    rw [Real.log_rpow hL0]
  have hexp : (r:ℝ)*(Real.log (8*(r:ℝ))-2*Real.log (L^(-100:ℝ))) ≤
      432*L^(1/(80:ℝ))*Real.log L := by
    rw [hlogV]
    calc
      _ ≤ (r:ℝ)*(216*Real.log L) := mul_le_mul_of_nonneg_left (by linarith) hr0.le
      _ ≤ (2*L^(1/(80:ℝ)))*(216*Real.log L) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by ring
  have hscalar : Real.log (432*Real.exp 1)+4*Real.log L+
      432*L^(1/(80:ℝ))*Real.log L ≤ L^(3/(100:ℝ)) := by
    have hbig : 1 ≤ L^(1/(80:ℝ))*Real.log L := one_le_mul_of_one_le_of_one_le hpow1 hLL
    have hc : Real.log (432*Real.exp 1) ≤
        |Real.log (432*Real.exp 1)| * (L^(1/(80:ℝ))*Real.log L) := by
      exact (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hbig)
    have hlog : Real.log L ≤ L^(1/(80:ℝ))*Real.log L :=
      le_mul_of_one_le_left (by positivity) hpow1
    calc
      _ ≤ L^(1/(80:ℝ))*((|Real.log (432*Real.exp 1)|+436)*Real.log L) := by nlinarith
      _ ≤ L^(1/(80:ℝ))*L^(7/(400:ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hL0.le _)
      _ = _ := by rw [← Real.rpow_add hL0]; norm_num
  have he := mrt_short_prime_sample_cost_exp hY hV hT
  have hfour : Real.exp (4*Real.log L) = L^4 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hL0] using
      Real.exp_nat_mul (Real.log L) 4
  change mrtShortPrimeSampleCost Y (L^(-100:ℝ)) T r ≤ _ at he ⊢
  calc
    _ ≤ (432*Real.exp 1*L^4)*Real.exp (432*L^(1/(80:ℝ))*Real.log L) :=
      he.trans (mul_le_mul hpref (Real.exp_le_exp.mpr hexp) (by positivity) (by positivity))
    _ = Real.exp (Real.log (432*Real.exp 1)+4*Real.log L+
        432*L^(1/(80:ℝ))*Real.log L) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by positivity : 0 < 432*Real.exp 1),
        hfour]
    _ ≤ _ := Real.exp_le_exp.mpr hscalar

/-- Uniform large-extra-prime sample cost. The remaining Mangoldt kernel
will have much stronger decay than this subexponential cardinality. -/
theorem mrt_extra_prime_sample_cost :
    ∀ᶠ L : ℝ in atTop, ∀ Y T : ℝ, 1 < Y →
      L^(79/(80:ℝ)) ≤ Real.log Y → Real.log Y ≤ L →
      1 < T → T ≤ Real.exp L →
      mrtShortPrimeSampleCost Y (L^(-100:ℝ)) T (mrtAmplificationOrder Y T) ≤
        Real.exp (L^(3/(100:ℝ))) := by
  let C := |Real.log (432*Real.exp 1)|+436
  have hC : 0 < C := by dsimp [C]; positivity
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ) < 7/400 by norm_num)).bound
    (show 0 < 1/C by positivity)
  filter_upwards [hb,eventually_ge_atTop (4:ℝ),
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)))] with L hb hL hLL
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg hlog0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hs : C*Real.log L ≤ L^(7/(400:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hb hC.le
    have he : C*((1/C)*L^(7/(400:ℝ)))=L^(7/(400:ℝ)) := by field_simp
    simpa only [he] using hh
  intro Y T hY hYL hYU hT hTU
  exact mrt_extra_sample_cost_pointwise hL hLL hs hY hYL hYU hT hTU

/-- The preceding optimized cost bounds the actual separated large-value
samples of every additional short prime interval. -/
theorem mrt_extra_prime_large_samples :
    ∀ᶠ L : ℝ in atTop, ∀ Y T : ℝ, 1 < Y →
      L^(79/(80:ℝ)) ≤ Real.log Y → Real.log Y ≤ L →
      1 < T → T ≤ Real.exp L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
      ∀ F : ℕ → ℂ, OneBounded F → ∀ S : Finset ℝ,
      (∀ t ∈ S, |t| ≤ T) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (∀ t ∈ S, L^(-100:ℝ) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖) →
      (S.card:ℝ) ≤ Real.exp (L^(3/(100:ℝ))) := by
  filter_upwards [mrt_extra_prime_sample_cost,eventually_gt_atTop (0:ℝ)] with L hL hL0
  intro Y T hY hYL hYU hT hTU P hP hbin F hF S hS hsep hlarge
  exact (mrt_short_prime_large_samples P hP hY hbin F hF
    (mrtAmplificationOrder Y T) (by linarith) (Real.rpow_pos_of_pos hL0 _)
    S hS hsep hlarge).trans (hL Y T hY hYL hYU hT hTU)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLargePrimeEnergy
namespace OAI

/-! The large-extra-prime branch of the actual cofactor product. The
only analytic premise here is the explicitly cited prime sparse input;
the large-value sample count and set-integral transfer are proved. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem HalaszPrimeSparseInput.large_prime_product_energy_oai
    (hprime : HalaszPrimeSparseInput) :
    ∃ C B₀ : ℝ, 0 < C ∧ 2 ≤ B₀ ∧ ∀ᶠ L : ℝ in atTop,
      ∀ H Y : ℝ, B₀ ≤ H → 2 ≤ Y → H^2 ≤ Y →
      L^(79/80:ℝ) ≤ Real.log Y → Real.log Y ≤ L → 1 ≤ Real.log Y →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
      (∀ p ∈ P, Real.log Y ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ Real.log Y+1/H) →
      OneBounded F →
      ∀ (A : Finset ℕ) (B : ℕ → ℂ) (N : ℕ) (a U : ℝ), 0 ≤ U →
      ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) →
      (∀ t ∈ E, L^(-100:ℝ) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖ →
        ‖mrtCofactorPolynomial A B N a t‖ ≤ U) →
      (∫ t in E ∩ {t | L^(-100:ℝ) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖},
        ‖mrtExponentialPolynomial P (fun p => F p/(p:ℂ))
          (fun p => -Real.log (p:ℝ)) t * mrtCofactorPolynomial A B N a t‖^2) ≤
        C*U^2/(H*(Real.log Y)^2) := by
  obtain ⟨C,B₀,hC,hB₀,hprime⟩ := hprime.short_prime_energy
  refine ⟨4*C,B₀,by positivity,hB₀,?_⟩
  filter_upwards [hprime,mrt_extra_prime_large_samples,eventually_ge_atTop (1:ℝ)]
    with L hprime hcount hL
  intro H Y hH hY hHY hYL hYU hlogY P F hP hwindow hF A B N a U _hU E hE hET hpoint
  let Q := mrtExponentialPolynomial P (fun p => F p/(p:ℂ))
    (fun p => -Real.log (p:ℝ))
  let R := mrtCofactorPolynomial A B N a
  let D := E ∩ {t | L^(-100:ℝ) ≤ ‖Q t‖}
  have hQc : Continuous Q := mrtExponentialPolynomial_continuous _ _ _
  have hRc : Continuous R := mrtCofactorPolynomial_continuous _ _ _ _
  have hD : MeasurableSet D := hE.inter (isClosed_le continuous_const hQc.norm).measurableSet
  have hDT : D ⊆ Set.Ioc (-Real.exp L) (Real.exp L) :=
    fun _ ht => hET ht.1
  have hsamples (S : Finset ℝ) (hS : ∀ t ∈ S, t ∈ D)
      (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) :
      (∑ t ∈ S, ‖Q t*R t‖^2) ≤ U^2*(C/(H*(Real.log Y)^2)) := by
    have hheight : ∀ t ∈ S, |t| ≤ Real.exp L := by
      intro t ht
      exact abs_le.mpr ⟨(hDT (hS t ht)).1.le,(hDT (hS t ht)).2⟩
    have hcard := hcount Y (Real.exp L) (by linarith) hYL hYU
      (Real.one_lt_exp_iff.mpr (by linarith)) le_rfl P
      (fun p hp => (hP p hp).1) (fun p hp => (hP p hp).2) F hF S hheight hsep
      (fun t ht => (hS t ht).2)
    have hp := hprime H Y hH hY hHY hYL hlogY P F hP hwindow hF S hheight hsep hcard
    calc
      _ = ∑ t ∈ S, ‖Q t‖^2*‖R t‖^2 := by
        apply sum_congr rfl
        intro t _
        rw [norm_mul,mul_pow]
      _ ≤ ∑ t ∈ S, ‖Q t‖^2*U^2 := by
        apply sum_le_sum
        intro t ht
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) (hpoint t (hS t ht).1 (hS t ht).2) 2
      _ = U^2*∑ t ∈ S, ‖Q t‖^2 := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro t _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (sq_nonneg U)
  have hi := mrt_set_integral_of_samples (fun t => ‖Q t*R t‖^2)
    ((hQc.mul hRc).norm.pow 2) (fun _ => sq_nonneg _) hD
    (Real.exp_pos L).le hDT hsamples
  change (∫ t in D, ‖Q t*R t‖^2) ≤ _
  apply hi.trans_eq
  ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.HalaszPrimeSparseInput.large_prime_product_energy_oai := @OAI.TwoPointCorrelations.HalaszPrimeSparseInput.large_prime_product_energy_oai
