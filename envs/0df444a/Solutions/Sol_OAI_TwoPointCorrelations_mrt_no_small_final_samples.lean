-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_no_small_final_samples
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:36:10.331108+00:00
-- url     : https://prove2.me/submissions/f8262d50-adf5-4624-ac2e-7aba1b609de6

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyExponents
namespace OAI

/-! The increasing prime-polynomial thresholds in MRT's multiscale
partition, indexed from zero to match `mrtFirstSmallBand`. -/

namespace TwoPointCorrelations



lemma mrtFrequencyExponent_bounds {η : ℝ} (hη : 0 ≤ η) (j : ℕ) :
    1 / 4 - 3 * η / 2 ≤ mrtFrequencyExponent η j ∧
      mrtFrequencyExponent η j ≤ 1 / 4 - η := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hi : (1 : ℝ) / (2 * ((j : ℝ) + 1)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hi0 : (0 : ℝ) ≤ 1 / (2 * ((j : ℝ) + 1)) := by positivity
  unfold mrtFrequencyExponent
  constructor
  · have hh := mul_le_mul_of_nonneg_left hi hη
    nlinarith
  · have hh := mul_nonneg hη hi0
    nlinarith

lemma mrtFrequencyExponent_nonneg {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 6)
    (j : ℕ) : 0 ≤ mrtFrequencyExponent η j := by
  have hh := (mrtFrequencyExponent_bounds hη j).1
  linarith




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyPartition
namespace OAI

/-! The first-small-band frequency partition. Every later class supplies
an actual large polynomial in the preceding band; the exceptional set is
exactly the set on which every band has a large polynomial. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical










theorem mrt_no_small_band_large_witness {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) {J j : ℕ} (hj : j < J)
    {t : ℝ} (ht : t ∈ mrtNoSmallBand K Q A J) :
    ∃ k ∈ K j, A j k < ‖Q j k t‖ := by
  have hn : t ∉ mrtSmallFrequencyBand K Q A j := by
    intro hsmall
    exact ht (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨mem_range.mpr hj, hsmall⟩⟩)
  simp only [mrtSmallFrequencyBand, Set.mem_ofPred_eq, not_forall, not_le, exists_prop] at hn
  exact hn


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTResolution
namespace OAI

/-! The logarithmic bin resolution used in the multiscale partition.
Its balance with the first prime threshold is exact. -/

namespace TwoPointCorrelations

open _root_.Finset



lemma mrtBaseResolution_pos (P Q η : ℝ) : 0 < mrtBaseResolution P Q η :=
  Real.exp_pos _









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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFinalSampleScale
namespace OAI

/-! The last ordinary prime band gives a separated-sample count strictly
below the square-root scale. This is the count needed by the integer
Gram kernel before the additional large-prime split. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma mrt_final_sample_cost_pointwise {L Y T α : ℝ}
    (hL : 4 ≤ L) (hLL : 16 ≤ Real.log L)
    (hsmall : |Real.log (432*Real.exp 1)|+6*Real.log L+Real.sqrt L ≤ L/200)
    (hY : 1 < Y) (hYL : 200*Real.log L ≤ Real.log Y)
    (hYU : Real.log Y ≤ Real.sqrt L) (hT : 1 < T) (hTU : T ≤ Real.exp L)
    (hα : 0 ≤ α) (hαu : α ≤ 6/25) :
    mrtShortPrimeSampleCost Y (Real.exp (-α*Real.log Y)) T
      (mrtAmplificationOrder Y T) ≤ Real.exp ((99/200:ℝ)*L) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogL0 : 0 ≤ Real.log L := by linarith
  have hlogY : 1 ≤ Real.log Y := by linarith
  have hlogY0 : 0 < Real.log Y := Real.log_pos hY
  have hlogT : Real.log T ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log (by linarith : 0 < T) hTU
  have hsqrt : Real.sqrt L ≤ L := Real.sqrt_le_self_iff.mpr (Or.inr hL1)
  have hYU' : Real.log Y ≤ L := hYU.trans hsqrt
  let r := mrtAmplificationOrder Y T
  have hrpos : 0 < r := by
    dsimp [r,mrtAmplificationOrder]
    exact Nat.ceil_pos.mpr (div_pos (Real.log_pos hT) hlogY0)
  have hr0 : (0:ℝ) < r := by exact_mod_cast hrpos
  have hr : (r:ℝ) ≤ Real.log T/Real.log Y+1 :=
    (mrt_amplification_order_bounds hY hT.le).2.2.le
  have hrL : (r:ℝ) ≤ 2*L := by
    have hd : Real.log T/Real.log Y ≤ L :=
      (div_le_div_of_nonneg_right hlogT hlogY0.le).trans
        (div_le_self hL0.le hlogY)
    linarith
  have hlog4 : Real.log (4*Y) ≤ 2*L := by
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by linarith : Y ≠ 0)]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)]
  have hrl : 0 ≤ (r:ℝ)*Real.log (4*Y) :=
    mul_nonneg hr0.le (Real.log_nonneg (by linarith))
  have hrlb : (r:ℝ)*Real.log (4*Y) ≤ 4*L^2 := by
    calc
      _ ≤ (2*L)*(2*L) := mul_le_mul hrL hlog4
        (Real.log_nonneg (by linarith)) (by positivity)
      _ = _ := by ring
  have hpref : 24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2) ≤
      432*Real.exp 1*L^4 := by
    have hs := pow_le_pow_left₀ hrl hrlb 2
    have hL4 : 1 ≤ L^4 := one_le_pow₀ hL1
    have he : (4*L^2)^2 = 16*L^4 := by ring
    rw [he] at hs
    have ht : 2+((r:ℝ)*Real.log (4*Y))^2 ≤ 18*L^4 := by nlinarith
    calc
      _ ≤ 24*Real.exp 1*(18*L^4) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have hlr : Real.log (8*(r:ℝ)) ≤ 2*Real.log L := by
    have hh := Real.log_le_log (by positivity : 0 < 8*(r:ℝ))
      (mul_le_mul_of_nonneg_left hrL (by norm_num : (0:ℝ) ≤ 8))
    rw [show (8:ℝ)*(2*L)=16*L by ring,
      Real.log_mul (by norm_num : (16:ℝ) ≠ 0) hL0.ne'] at hh
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)]
  have hratio : (L/Real.log Y)*(2*Real.log L) ≤ L/100 := by
    have hh := mul_le_mul_of_nonneg_left hYL (show 0 ≤ L/100 by positivity)
    calc
      _ = (L*(2*Real.log L))/Real.log Y := by ring
      _ ≤ L/100 := (div_le_iff₀ hlogY0).mpr (by nlinarith)
  have hentropy : (r:ℝ)*Real.log (8*(r:ℝ)) ≤ L/100+2*Real.log L := by
    have hrr : (r:ℝ) ≤ L/Real.log Y+1 :=
      hr.trans (add_le_add (div_le_div_of_nonneg_right hlogT hlogY0.le) le_rfl)
    calc
      _ ≤ (L/Real.log Y+1)*(2*Real.log L) :=
        mul_le_mul hrr hlr (Real.log_nonneg (by exact_mod_cast
          (show 1 ≤ 8*r by omega))) (by positivity)
      _ = (L/Real.log Y)*(2*Real.log L)+2*Real.log L := by ring
      _ ≤ _ := by linarith
  have horder : (r:ℝ)*Real.log Y ≤ L+Real.sqrt L := by
    have hh := mul_le_mul_of_nonneg_right hr hlogY0.le
    have he : (Real.log T/Real.log Y+1)*Real.log Y = Real.log T+Real.log Y := by
      rw [add_mul,div_mul_cancel₀ _ hlogY0.ne',one_mul]
    rw [he] at hh
    linarith
  have hthreshold : (r:ℝ)*(2*α*Real.log Y) ≤ (12/25:ℝ)*(L+Real.sqrt L) := by
    calc
      _ = (2*α)*((r:ℝ)*Real.log Y) := by ring
      _ ≤ (2*α)*(L+Real.sqrt L) := mul_le_mul_of_nonneg_left horder (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hexp : (r:ℝ)*(Real.log (8*(r:ℝ))-
      2*Real.log (Real.exp (-α*Real.log Y))) ≤
      L/100+2*Real.log L+(12/25:ℝ)*(L+Real.sqrt L) := by
    rw [Real.log_exp]
    nlinarith
  have hscalar : Real.log (432*Real.exp 1)+4*Real.log L+
      (L/100+2*Real.log L+(12/25:ℝ)*(L+Real.sqrt L)) ≤ (99/200:ℝ)*L := by
    have ha := le_abs_self (Real.log (432*Real.exp 1))
    have hs := Real.sqrt_nonneg L
    linarith
  have hfour : Real.exp (4*Real.log L)=L^4 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hL0] using Real.exp_nat_mul (Real.log L) 4
  have hc := mrt_short_prime_sample_cost_exp hY (Real.exp_pos (-α*Real.log Y)) hT
  change mrtShortPrimeSampleCost Y (Real.exp (-α*Real.log Y)) T r ≤ _ at hc ⊢
  calc
    _ ≤ (432*Real.exp 1*L^4)*Real.exp
        (L/100+2*Real.log L+(12/25:ℝ)*(L+Real.sqrt L)) :=
      hc.trans (mul_le_mul hpref (Real.exp_le_exp.mpr hexp) (by positivity) (by positivity))
    _ = Real.exp (Real.log (432*Real.exp 1)+4*Real.log L+
        (L/100+2*Real.log L+(12/25:ℝ)*(L+Real.sqrt L))) := by
      conv_rhs =>
        rw [Real.exp_add,Real.exp_add,
          Real.exp_log (by positivity : 0 < 432*Real.exp 1),hfour]
    _ ≤ _ := Real.exp_le_exp.mpr hscalar

/-- Fixed eta=1/100 leaves a strict power saving below square-root sample
size. The endpoint assumptions are only on the actual short prime bin. -/
theorem mrt_final_prime_sample_cost :
    ∀ᶠ L : ℝ in atTop, ∀ Y T α : ℝ, 1 < Y →
      200*Real.log L ≤ Real.log Y → Real.log Y ≤ Real.sqrt L →
      1 < T → T ≤ Real.exp L → 0 ≤ α → α ≤ 6/25 →
      mrtShortPrimeSampleCost Y (Real.exp (-α*Real.log Y)) T
        (mrtAmplificationOrder Y T) ≤ Real.exp ((99/200:ℝ)*L) := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)).bound
    (show (0:ℝ)<1/3600 by norm_num)
  filter_upwards [hb,eventually_ge_atTop (360000:ℝ),
    eventually_ge_atTop (600*|Real.log (432*Real.exp 1)|),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (16:ℝ))]
    with L hb hL hC hLL
  have hL0 : 0 < L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ Real.log L),
    Real.norm_eq_abs,Real.rpow_one,abs_of_pos hL0] at hb
  have hsqrt : Real.sqrt L ≤ L/600 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hh := mul_nonneg (show 0 ≤ L-360000 by linarith) hL0.le
      nlinarith
  have hsmall : |Real.log (432*Real.exp 1)|+6*Real.log L+Real.sqrt L ≤ L/200 := by
    linarith
  intro Y T α hY hYL hYU hT hTU hα hαu
  exact mrt_final_sample_cost_pointwise (by linarith) hLL hsmall hY hYL hYU hT hTU hα hαu

/-- Application to the literal finite prime polynomial. -/
theorem mrt_final_prime_large_samples :
    ∀ᶠ L : ℝ in atTop, ∀ Y T α : ℝ, 1 < Y →
      200*Real.log L ≤ Real.log Y → Real.log Y ≤ Real.sqrt L →
      1 < T → T ≤ Real.exp L → 0 ≤ α → α ≤ 6/25 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
      ∀ F : ℕ → ℂ, OneBounded F → ∀ S : Finset ℝ,
      (∀ t ∈ S, |t| ≤ T) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (∀ t ∈ S, Real.exp (-α*Real.log Y) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖) →
      (S.card:ℝ) ≤ Real.exp ((99/200:ℝ)*L) := by
  filter_upwards [mrt_final_prime_sample_cost] with L hL
  intro Y T α hY hYL hYU hT hTU hα hαu P hP hbin F hF S hS hsep hlarge
  exact (mrt_short_prime_large_samples P hP hY hbin F hF
    (mrtAmplificationOrder Y T) (by linarith) (Real.exp_pos _)
    S hS hsep hlarge).trans (hL Y T α hY hYL hYU hT hTU hα hαu)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallCount
namespace OAI

/-! The optimized moment applied to every actual logarithmic bin in the
last-band witness cover. No abstract covering family is assumed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem mrt_no_small_final_samples_oai :
    ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ T : ℝ, 1 < T → T ≤ Real.exp L → ∀ S : Finset ℝ,
    (∀ t ∈ S, |t| ≤ T) →
    (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
    (∀ t ∈ S, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (S.card:ℝ) ≤ (mrtLogFamilyBins P Q (1/100) j).card *
      Real.exp ((99/200:ℝ)*L) := by
  filter_upwards [mrt_final_prime_large_samples,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with L hfinal hLL
  intro V F hF J j hj P Q hQ hres hprime hrange hlo hhi T hT hTU S hS hsep hno
  let H := mrtResolution P Q (1/100) (j+1)
  let K := mrtLogFamilyBins P Q (1/100) j
  let S' := fun k => S.filter (fun t => mrtLogFamilyThreshold P Q (1/100) j k <
    ‖mrtLogFamilyPolynomial V F P Q (1/100) j k t‖)
  have hH : 2 ≤ H := by
    have hj1 : (1:ℝ) ≤ (j+1:ℕ) := by exact_mod_cast (show 1 ≤ j+1 by omega)
    have hs : 1 ≤ ((j+1:ℕ):ℝ)^2 := one_le_pow₀ hj1
    dsimp [H,mrtResolution]
    nlinarith [mrtBaseResolution_pos P Q (1/100)]
  have hH0 : 0 < H := by linarith
  have hBU : 1 ≤ mrtBandUpper Q (j+1) := by
    have hlogQ : 0 ≤ Real.log Q := by linarith
    unfold mrtBandUpper
    exact Real.one_le_exp (by positivity)
  have hd := mrt_log_bin_prime_data (V (j+1)) hH (Real.exp_pos _) hprime hrange
  have hcover : S ⊆ K.biUnion S' := by
    intro t ht
    obtain ⟨k,hk,htk⟩ := mrt_no_small_band_large_witness
      (mrtLogFamilyBins P Q (1/100)) (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) hj (hno t ht)
    exact mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨ht,htk⟩⟩
  have hcard : (S.card:ℝ) ≤ ∑ k ∈ K, ((S' k).card:ℝ) := by
    exact_mod_cast (card_le_card hcover).trans card_biUnion_le
  apply hcard.trans
  calc
    _ ≤ ∑ _k ∈ K, Real.exp ((99/200:ℝ)*L) := by
      apply sum_le_sum
      intro k hk
      let Y := mrtPrimeLogLower H k
      have hYlow : 200*Real.log L ≤ Real.log Y := by
        have hh := mrt_log_bin_lower_endpoint (by linarith : 1 ≤ H)
          (Real.exp_pos _) (mem_Icc.mp hk).1
        have hh' := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hh
        rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp] at hh'
        change -1+Real.log (mrtBandLower P Q (j+1)) ≤ Real.log Y at hh'
        linarith
      have hY : 1 < Y := (Real.one_lt_exp_iff.mpr
        (show 0 < (k:ℝ)/H by
          have hh : 0 < Real.log Y := by linarith
          simpa only [Y,mrtPrimeLogLower,Real.log_exp] using hh))
      have hYhi : Real.log Y ≤ Real.sqrt L :=
        (Real.log_le_log (by linarith : 0 < Y)
          (mrt_prime_log_lower_le_upper hH0 hBU (mem_Icc.mp hk).2)).trans hhi
      let α := mrtFrequencyExponent (1/100) j
      have hα : 0 ≤ α := mrtFrequencyExponent_nonneg (by norm_num) (by norm_num) j
      have hαu : α ≤ 6/25 := by
        have hh := (mrtFrequencyExponent_bounds (show (0:ℝ) ≤ 1/100 by norm_num) j).2
        exact hh.trans_eq (by norm_num)
      apply hfinal Y T α hY hYlow hYhi hT hTU hα hαu
        ((V (j+1)).filter (fun p => mrtPrimeLogBin H p = k))
        (fun p hp => hprime p (mem_filter.mp hp).1)
        (fun p hp => ?_) F hF (S' k)
        (fun t ht => hS t (mem_filter.mp ht).1)
        (fun t ht s hs hts => hsep t (mem_filter.mp ht).1 s (mem_filter.mp hs).1 hts)
        (fun t ht => ?_)
      · have hh := hd.2 p (mem_filter.mp hp).1
        have hu := hh.2.trans (mul_le_mul_of_nonneg_right
          (mrt_prime_log_width hH).2.1 (Real.exp_pos _).le)
        simpa only [(mem_filter.mp hp).2] using And.intro hh.1 hu
      · exact (mem_filter.mp ht).2.le
    _ = _ := by simp [K]

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_no_small_final_samples_oai := @OAI.TwoPointCorrelations.mrt_no_small_final_samples_oai
