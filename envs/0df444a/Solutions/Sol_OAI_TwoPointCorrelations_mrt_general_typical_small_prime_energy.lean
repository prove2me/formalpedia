-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_general_typical_small_prime_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:31:27.361873+00:00
-- url     : https://prove2.me/submissions/ead8733a-61a0-4a3d-9a84-826f12cb0378

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical






lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl









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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBoundaryMean
namespace OAI

/-! The two boundary strips created by replacing prime-dependent
cofactor cutoffs with endpoints of a multiplicative prime bin. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory


lemma mrt_mem_boundary_iff (N n : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) :
    n ∈ mrtBoundarySet N δ ↔
      (N < n ∧ (n : ℝ) ≤ δ * N) ∨
        (2 * N < n ∧ (n : ℝ) ≤ δ * (2 * N : ℕ)) := by
  have hδ0 : 0 ≤ δ := by linarith
  simp only [mrtBoundarySet, mem_union, mem_Ioc,
    Nat.le_floor_iff (mul_nonneg hδ0 (Nat.cast_nonneg N)),
    Nat.le_floor_iff (mul_nonneg hδ0 (Nat.cast_nonneg (2 * N)))]

lemma mrt_boundary_strip_card (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) :
    ((Ioc N ⌊δ * (N : ℝ)⌋₊).card : ℝ) ≤ (δ - 1) * N := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl : (N : ℝ) ≤ δ * N := by nlinarith
  have hf : N ≤ ⌊δ * (N : ℝ)⌋₊ := Nat.le_floor hl
  rw [Nat.card_Ioc, Nat.cast_sub hf]
  have hu := Nat.floor_le (show 0 ≤ δ * (N : ℝ) by positivity)
  nlinarith

theorem mrt_boundary_card (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) :
    ((mrtBoundarySet N δ).card : ℝ) ≤ 3 * (δ - 1) * N := by
  have hc := card_union_le (Ioc N ⌊δ * (N : ℝ)⌋₊)
    (Ioc (2 * N) ⌊δ * (2 * N : ℕ)⌋₊)
  have hc' : ((mrtBoundarySet N δ).card : ℝ) ≤
      ((Ioc N ⌊δ * (N : ℝ)⌋₊).card : ℝ) +
        ((Ioc (2 * N) ⌊δ * (2 * N : ℕ)⌋₊).card : ℝ) := by
    exact_mod_cast hc
  have h1 := mrt_boundary_strip_card N hδ
  have h2 := mrt_boundary_strip_card (2 * N) hδ
  conv at h2 => rhs; rw [Nat.cast_mul, Nat.cast_ofNat]
  linarith

lemma mrt_boundary_range {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : δ ≤ 2)
    {n : ℕ} (hn : n ∈ mrtBoundarySet N δ) : N < n ∧ n ≤ 4 * N := by
  have hn' := mem_union.mp hn
  have hh : ∀ M : ℕ, ⌊δ * (M : ℝ)⌋₊ ≤ 2 * M := by
    intro M
    apply Nat.floor_le_of_le
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right hδ (show (0 : ℝ) ≤ M from Nat.cast_nonneg M)
  rcases hn' with hn' | hn'
  · have hd := mem_Ioc.mp hn'
    exact ⟨hd.1, (hd.2.trans (hh N)).trans (by omega)⟩
  · have hd := mem_Ioc.mp hn'
    have hu := hd.2.trans (hh (2 * N))
    exact ⟨by omega, by omega⟩

/-- Arbitrary bounded coefficients on the two bin-boundary strips have
mean-square cost proportional to their multiplicative width. -/
theorem mrt_boundary_mean_square (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hb : ∀ n ∈ mrtBoundarySet N δ, ‖b n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial (mrtBoundarySet N δ)
      (fun n => b n / (n : ℂ)) (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      96 * Real.exp 1 * (T / (N : ℝ) + 1) * (δ - 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrange : mrtBoundarySet N δ ⊆ Ioc 0 (4 * N) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mrt_boundary_range hN hδ2 hn
    exact mem_Ioc.mpr ⟨by omega, hn2⟩
  have hcoeff : (∑ n ∈ mrtBoundarySet N δ, ‖b n / (n : ℂ)‖ ^ 2) ≤
      3 * (δ - 1) / (N : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ mrtBoundarySet N δ, (1 / (N : ℝ)) ^ 2 := by
        apply sum_le_sum
        intro n hn
        rw [norm_div, Complex.norm_natCast]
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div₀ (by norm_num) (hb n hn) hNr
          (by exact_mod_cast (mrt_boundary_range hN hδ2 hn).1.le)
      _ = ((mrtBoundarySet N δ).card : ℝ) * (1 / (N : ℝ)) ^ 2 := by simp
      _ ≤ (3 * (δ - 1) * N) * (1 / (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (mrt_boundary_card N hδ) (by positivity)
      _ = _ := by field_simp
  apply (mrt_dirichlet_mean_square_subset (mrtBoundarySet N δ) hrange
    (fun n => b n / (n : ℂ)) hT).trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (4 * N : ℕ)) * (3 * (δ - 1) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = 24 * Real.exp 1 * (T / (N : ℝ) + 4) * (δ - 1) := by
      push_cast
      field_simp; ring
    _ ≤ _ := by
      have hd : 0 ≤ Real.exp 1 * (δ - 1) := mul_nonneg (Real.exp_pos _).le (by linarith)
      have ht := mul_nonneg (div_nonneg hT.le hNr.le) hd
      nlinarith

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




lemma mrt_norm_sum_sq_le_card {α : Type*} (S : Finset α) (a : α → ℂ) :
    ‖∑ i ∈ S, a i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ S, ‖a i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖a i‖)


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

/-- Frequency-restricted Cauchy--Schwarz, with the actual pointwise
short-prime bounds and the cofactor energies left explicit. -/
theorem mrt_restricted_product_sum_energy {ι : Type*} (J : Finset ι)
    (Q R : ι → ℝ → ℂ) (hR : ∀ j ∈ J, Continuous (R j))
    (A : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hQ : ∀ j ∈ J, ∀ t ∈ E, ‖Q j t‖ ≤ A j) :
    (∫ t in E, ‖∑ j ∈ J, Q j t * R j t‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 *
        (∫ t in -T..T, ‖R j t‖ ^ 2) := by
  have hi (j : ι) (hj : j ∈ J) := mrt_continuous_square_integrable (hR j hj) hT hE
  calc
    _ ≤ ∫ t in E, (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * ‖R j t‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((integrable_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))).const_mul _)
      intro t ht
      apply (mrt_norm_sum_sq_le_card J (fun j => Q j t * R j t)).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j hj
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hQ j hj t ht) 2) (sq_nonneg _)
    _ = (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * (∫ t in E, ‖R j t‖ ^ 2) := by
      rw [integral_const_mul, integral_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))]
      simp only [integral_const_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (mrt_restricted_square_le_interval (hR j hj) hT hE) (sq_nonneg _)

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix
namespace OAI

/-! Exact change of variables `x=u*z` for a divisibility indicator,
including the floor endpoint `floor(X/u)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_eq_Icc (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix F X = ∑ n ∈ Icc 1 X, F n := by
  simpa only [Nat.zero_add, positivePrefix] using (sum_Icc_shift F 0 X).symm

theorem divisibility_positivePrefix (F : ℕ → ℂ) (u X : ℕ) (hu : 0 < u) :
    positivePrefix (fun n => natDivisibilityIndicator u n * F n) X =
      positivePrefix (fun z => F (u * z)) (X / u) := by
  calc
    _ = ∑ n ∈ (Icc 1 X).filter (fun n => u ∣ n), F n := by
      rw [positivePrefix_eq_Icc, sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : u ∣ n <;> simp only [natDivisibilityIndicator, hn, ite_true, ite_false,
        one_mul, zero_mul]
    _ = ∑ z ∈ Icc 1 (X / u), F (u * z) := by
      symm
      apply sum_bij (fun z _ => u * z)
      · intro z hz
        obtain ⟨hz₁, hzX⟩ := mem_Icc.mp hz
        apply mem_filter.mpr
        refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hu hz₁, ?_⟩, dvd_mul_right u z⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hu).mp hzX
      · intro z _ w _ heq
        exact Nat.eq_of_mul_eq_mul_left hu heq
      · intro n hn
        obtain ⟨hnI, hdiv⟩ := mem_filter.mp hn
        obtain ⟨hn₁, hnX⟩ := mem_Icc.mp hnI
        refine ⟨n / u, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnX⟩, Nat.mul_div_cancel' hdiv⟩
        exact Nat.div_pos (Nat.le_of_dvd hn₁ hdiv) hu
      · intro z _
        rfl
    _ = _ := (positivePrefix_eq_Icc (fun z => F (u * z)) (X / u)).symm

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

lemma finitePrimeDivisorCount_insert {P : Finset ℕ} {p : ℕ} (hp : p ∉ P) (n : ℕ) :
    finitePrimeDivisorCount (insert p P) n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount P n := by
  simp only [finitePrimeDivisorCount, sum_insert hp]

lemma finitePrimeDivisorCount_pos_of_mem {P : Finset ℕ} {p n : ℕ}
    (hp : p ∈ P) (hpn : p ∣ n) : 0 < finitePrimeDivisorCount P n := by
  rw [finitePrimeDivisorCount_eq_card, card_pos]
  exact ⟨p, mem_filter.mpr ⟨hp, hpn⟩⟩

/-- The correction term distinguishes a new prime from a repeated prime. -/
theorem mrt_prime_divisor_count_mul (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) (m : ℕ) :
    finitePrimeDivisorCount P (p * m) =
      (if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m := by
  have hc (n : ℕ) : finitePrimeDivisorCount P n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount (P.erase p) n := by
    conv_lhs => rw [← insert_erase hp]
    exact finitePrimeDivisorCount_insert (notMem_erase p P) n
  have he : finitePrimeDivisorCount (P.erase p) (p * m) =
      finitePrimeDivisorCount (P.erase p) m := by
    unfold finitePrimeDivisorCount
    apply sum_congr rfl
    intro q hq
    have hq' := mem_erase.mp hq
    have hqprime := hP q hq'.2
    have hqp : ¬q ∣ p := by
      intro hdiv
      exact hq'.1 ((Nat.prime_dvd_prime_iff_eq hqprime (hP p hp)).mp hdiv)
    simp only [hqprime.dvd_mul, hqp, false_or]
  rw [hc (p * m), hc m, he]
  simp only [dvd_mul_right, ite_true]
  split_ifs <;> omega

lemma mrt_ramare_common_denominator (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    (∑ p ∈ P, if p ∣ n then F n / (finitePrimeDivisorCount P n : ℂ) else 0) =
      if finitePrimeDivisorCount P n = 0 then 0 else F n := by
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, ← finitePrimeDivisorCount_eq_card]
  by_cases hn : finitePrimeDivisorCount P n = 0
  · simp [hn]
  · rw [if_neg hn]
    have hn' : (finitePrimeDivisorCount P n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp

/-- Corrected pointwise factorization, with no squarefree assumption. -/
theorem mrt_ramare_identity (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (n : ℕ) :
    (if finitePrimeDivisorCount P n = 0 then 0 else F n) =
      ∑ p ∈ P, if p ∣ n then
        F (p * (n / p)) /
          (((if p ∣ n / p then 0 else 1) + finitePrimeDivisorCount P (n / p) : ℕ) : ℂ)
        else 0 := by
  rw [← mrt_ramare_common_denominator P F n]
  apply sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · simp only [hpn, ite_true]
    have he := Nat.mul_div_cancel' hpn
    have hc := mrt_prime_divisor_count_mul P hP hp (n / p)
    rw [he] at hc ⊢
    rw [hc]
  · simp only [hpn, ite_false]


lemma mrt_inverse_successor_difference {k : ℕ} (hk : 0 < k) :
    ‖(k : ℂ)⁻¹ - ((k + 1 : ℕ) : ℂ)⁻¹‖ ≤ 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1C : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have he : (k : ℂ)⁻¹ - ((k + 1 : ℕ) : ℂ)⁻¹ =
      ((1 / ((k : ℝ) * (k + 1)) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  apply (div_le_one (by positivity)).mpr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- Replacing the corrected denominator by `ω_P(m)+1` costs only the
prime-square terms.  This is the correction explicitly needed in MRT v3. -/
theorem mrt_ramare_denominator_error (P : Finset ℕ) {p m : ℕ}
    (hp : p ∈ P) (z : ℂ) :
    ‖z / (((if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m : ℕ) : ℂ) -
      z / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)‖ ≤
        if p ∣ m then ‖z‖ else 0 := by
  by_cases hpm : p ∣ m
  · simp only [hpm, ite_true, zero_add]
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, norm_mul]
    have hk := finitePrimeDivisorCount_pos_of_mem hp hpm
    exact (mul_le_mul_of_nonneg_left (mrt_inverse_successor_difference hk)
      (norm_nonneg z)).trans_eq (mul_one _)
  · simp only [hpm, ite_false, Nat.add_comm 1, sub_self, norm_zero, le_refl]


lemma mrt_count_multiples {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ m ∈ Icc 1 N, if p ∣ m then (1 : ℝ) else 0) = (N / p : ℕ) := by
  have he := divisibility_positivePrefix (fun _ => (1 : ℂ)) p N hp
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, mul_one,
    sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum, apply_ite, Complex.one_re, Complex.zero_re,
    Complex.natCast_re] using hr


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeSquareMean
namespace OAI

/-! The prime-square error in the corrected Ramaré decomposition has a
small mean square.  The count is evaluated by pairing prime-square
divisibility tests; distinct primes give the product modulus exactly. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrtPrimeSquareCount_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ mrtPrimeSquareCount P n := by
  unfold mrtPrimeSquareCount
  exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

lemma mrt_prime_square_joint_count (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (∑ n ∈ Icc 1 N, (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
      (if q ^ 2 ∣ n then (1 : ℝ) else 0)) ≤
      (N : ℝ) * ((if p = q then 1 / (p : ℝ) ^ 2 else 0) +
        (1 / (p : ℝ) ^ 2) * (1 / (q : ℝ) ^ 2)) := by
  by_cases hpq : p = q
  · subst q
    have he (n : ℕ) : (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if p ^ 2 ∣ n then (1 : ℝ) else 0) =
        (if p ^ 2 ∣ n then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    rw [mrt_count_multiples (pow_pos hp.pos 2)]
    simp only [ite_true]
    calc
      _ ≤ (N : ℝ) / (p ^ 2 : ℕ) := Nat.cast_div_le
      _ = (N : ℝ) * (1 / (p : ℝ) ^ 2) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (Nat.cast_nonneg N)
  · have hc : Nat.Coprime (p ^ 2) (q ^ 2) := ((Nat.coprime_primes hp hq).mpr hpq).pow 2 2
    have hd (n : ℕ) : p ^ 2 * q ^ 2 ∣ n ↔ p ^ 2 ∣ n ∧ q ^ 2 ∣ n := by
      constructor
      · intro h
        exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩
      · rintro ⟨h1, h2⟩
        exact hc.mul_dvd_of_dvd_of_dvd h1 h2
    have he (n : ℕ) : (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if q ^ 2 ∣ n then (1 : ℝ) else 0) =
        (if p ^ 2 * q ^ 2 ∣ n then (1 : ℝ) else 0) := by
      simp only [hd]
      split_ifs <;> simp_all
    simp_rw [he]
    rw [mrt_count_multiples (Nat.mul_pos (pow_pos hp.pos 2) (pow_pos hq.pos 2)),
      if_neg hpq, zero_add]
    convert (preTransparency := .instances) (Nat.cast_div_le (m := N) (n := p ^ 2 * q ^ 2) :
      ((N / (p ^ 2 * q ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / (p ^ 2 * q ^ 2 : ℕ)) using 1
    push_cast
    ring

/-- No logarithm or cardinality of the prime set occurs in the
divisibility-count second moment. -/
theorem mrt_prime_square_count_second_moment (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (mrtPrimeSquareCount P n) ^ 2) ≤
      (N : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have he (n : ℕ) : (mrtPrimeSquareCount P n) ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if q ^ 2 ∣ n then (1 : ℝ) else 0) := by
    unfold mrtPrimeSquareCount
    rw [pow_two, sum_mul]
    apply sum_congr rfl
    intro p _
    rw [mul_sum]
  simp_rw [he]
  rw [sum_comm (s := Icc 1 N) (t := P)]
  calc
    _ = ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Icc 1 N,
        (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if q ^ 2 ∣ n then (1 : ℝ) else 0) := by
      apply sum_congr rfl
      intro p _
      exact sum_comm
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, (N : ℝ) *
        ((if p = q then 1 / (p : ℝ) ^ 2 else 0) +
          (1 / (p : ℝ) ^ 2) * (1 / (q : ℝ) ^ 2)) := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro q hq
      exact mrt_prime_square_joint_count N p q (hP p hp) (hP q hq)
    _ = _ := by
      simp_rw [← mul_sum]
      congr 1
      simp only [sum_add_distrib]
      congr 1
      · apply sum_congr rfl
        intro p hp
        simp [hp]
      · calc
          _ = ∑ p ∈ P, (1 / (p : ℝ) ^ 2) * (∑ q ∈ P, 1 / (q : ℝ) ^ 2) := by
            apply sum_congr rfl
            intro p _
            exact (mul_sum _ _ _).symm
          _ = _ := by rw [← sum_mul, pow_two]

theorem mrt_prime_square_coefficient_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (2 * N), ‖b n‖ ≤ mrtPrimeSquareCount P n) :
    (∑ n ∈ Ioc N (2 * N), ‖b n / (n : ℂ)‖ ^ 2) ≤
      (2 / (N : ℝ)) * ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ n ∈ Ioc N (2 * N), ((mrtPrimeSquareCount P n) / (N : ℝ)) ^ 2 := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_natCast]
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div₀ (mrtPrimeSquareCount_nonneg P n) (hb n hn) hNr
        (by exact_mod_cast (mem_Ioc.mp hn).1.le)
    _ = (N : ℝ)⁻¹ ^ 2 * ∑ n ∈ Ioc N (2 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      simp_rw [div_eq_mul_inv, mul_pow]
      rw [← sum_mul, mul_comm]
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ∑ n ∈ Icc 1 (2 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      · exact fun _ _ _ => sq_nonneg _
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ((2 * N : ℕ) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_count_second_moment P hP (2 * N))
        (by positivity)
    _ = _ := by
      push_cast
      field_simp

/-- The mean-square cost of any prime-square-supported Ramaré error. -/
theorem mrt_prime_square_dyadic_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (2 * N), ‖b n‖ ≤ mrtPrimeSquareCount P n)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial b N t‖ ^ 2) ≤
      32 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := mrt_dirichlet_mean_square_subset (Ioc N (2 * N)) (N := 2 * N)
    (by intro n hn; exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,
      (mem_Ioc.mp hn).2⟩) (fun n => b n / (n : ℂ)) hT
  apply hm.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (2 * N : ℕ)) * ((2 / (N : ℝ)) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_coefficient_mass P hP b hN hb)
        (by positivity)
    _ = 16 * Real.exp 1 * (T / (N : ℝ) + 2) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
      push_cast
      field_simp; ring
    _ ≤ _ := by
      have hc : 0 ≤ (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 := by positivity
      nlinarith [mul_nonneg (Real.exp_pos 1).le hc,
        mul_nonneg (div_nonneg hT.le hNr.le) (mul_nonneg (Real.exp_pos 1).le hc)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRamareMeanError
namespace OAI

/-! The actual coefficient error made by replacing the corrected Ramaré
denominator with `ω_P(m)+1`.  The pointwise error is supported on prime
squares, so the preceding second-moment count applies directly. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem mrt_ramare_correction_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (n : ℕ) :
    ‖mrtRamareCorrection P F n‖ ≤ ‖F n‖ * mrtPrimeSquareCount P n := by
  unfold mrtRamareCorrection
  rw [mrt_ramare_identity P hP F n, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, if p ^ 2 ∣ n then ‖F n‖ else 0 := by
      apply sum_le_sum
      intro p hp
      by_cases hpn : p ∣ n
      · simp only [hpn, ite_true, Nat.mul_div_cancel' hpn]
        have he : p ∣ n / p ↔ p ^ 2 ∣ n := by
          simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hpn : p ∣ n / p ↔ p * p ∣ n)
        simpa only [he] using mrt_ramare_denominator_error P hp (F n) (m := n / p)
      · have hs : ¬p ^ 2 ∣ n := by
          intro hn
          apply hpn
          exact dvd_trans (by simpa only [pow_two] using (dvd_mul_right p p)) hn
        simp only [hpn, hs, ite_false, sub_self, norm_zero, le_refl]
    _ = _ := by
      unfold mrtPrimeSquareCount
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      split_ifs <;> simp

theorem mrt_ramare_correction_oneBounded (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (hF : OneBounded F)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtRamareCorrection P F n‖ ≤ mrtPrimeSquareCount P n := by
  apply (mrt_ramare_correction_bound P hP F n).trans
  exact (mul_le_mul_of_nonneg_right (hF n hn) (mrtPrimeSquareCount_nonneg P n)).trans_eq
    (one_mul _)

/-- The literal denominator correction costs only the reciprocal square
mass in the normalized dyadic mean square.  Multiplicativity is not
needed for this error estimate. -/
theorem mrt_ramare_correction_mean_square (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtRamareCorrection P F) N t‖ ^ 2) ≤
      32 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  apply mrt_prime_square_dyadic_mean P hP _ hN _ hT
  intro n hn
  exact mrt_ramare_correction_oneBounded P hP F hF (hN.trans (mem_Ioc.mp hn).1)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRamareWeights
namespace OAI

/-! Positive coefficient weights in the uncorrected Ramaré polynomial.
They have total mass at most one, even at integers divisible by prime
squares.  This is the contraction needed for logarithmic-bin cutoffs. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mrtRamareWeight_nonneg (P : Finset ℕ) (n p : ℕ) :
    0 ≤ mrtRamareWeight P n p := by
  unfold mrtRamareWeight
  split_ifs <;> positivity

lemma mrt_ramare_weight_le_count (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p n : ℕ} (hp : p ∈ P) (hpn : p ∣ n) :
    mrtRamareWeight P n p ≤ 1 / (finitePrimeDivisorCount P n : ℝ) := by
  have hcount := mrt_prime_divisor_count_mul P hP hp (n / p)
  rw [Nat.mul_div_cancel' hpn] at hcount
  have hc : finitePrimeDivisorCount P n ≤ finitePrimeDivisorCount P (n / p) + 1 := by
    rw [hcount]
    split_ifs <;> omega
  have hpos : (0 : ℝ) < finitePrimeDivisorCount P n := by
    exact_mod_cast finitePrimeDivisorCount_pos_of_mem hp hpn
  rw [mrtRamareWeight, if_pos hpn]
  exact one_div_le_one_div_of_le hpos (by exact_mod_cast hc)

theorem mrt_ramare_weight_sum_le_one (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∑ p ∈ P, mrtRamareWeight P n p) ≤ 1 := by
  by_cases hc : finitePrimeDivisorCount P n = 0
  · have hz : ∀ p ∈ P, ¬p ∣ n := by
      intro p hp hpn
      have := finitePrimeDivisorCount_pos_of_mem hp hpn
      omega
    have hs : (∑ p ∈ P, mrtRamareWeight P n p) = 0 := by
      apply sum_eq_zero
      intro p hp
      simp only [mrtRamareWeight, if_neg (hz p hp)]
    rw [hs]
    norm_num
  · calc
      _ ≤ ∑ p ∈ P, if p ∣ n then 1 / (finitePrimeDivisorCount P n : ℝ) else 0 := by
        apply sum_le_sum
        intro p hp
        by_cases hpn : p ∣ n
        · rw [if_pos hpn]
          exact mrt_ramare_weight_le_count P hP hp hpn
        · simp only [mrtRamareWeight, if_neg hpn, le_refl]
      _ = 1 := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, ← finitePrimeDivisorCount_eq_card]
        exact mul_one_div_cancel (by exact_mod_cast hc)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCoarseBins
namespace OAI

/-! Coarse cofactor windows for a multiplicative prime bin.  The weights
are the actual Ramaré weights, and moving all primes in a bin to its
lower endpoint changes coefficients only in two short boundary strips. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mrtCoarseRamareWeight_nonneg (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ) :
    0 ≤ mrtCoarseRamareWeight P L N n := by
  apply sum_nonneg
  intro p _
  exact mul_nonneg (mrtRamareWeight_nonneg P n p) (by split_ifs <;> norm_num)

lemma mrt_coarse_weight_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (L : ℕ → ℝ) (N n : ℕ) : mrtCoarseRamareWeight P L N n ≤ 1 := by
  apply le_trans _ (mrt_ramare_weight_sum_le_one P hP n)
  apply sum_le_sum
  intro p _
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]
    exact mrtRamareWeight_nonneg P n p

lemma mrt_coarse_window_support {X δ a p m n : ℝ} (hδ : 1 ≤ δ)
    (hm : 0 ≤ m) (hl : a ≤ p) (hu : p ≤ δ * a) (hn : p * m = n)
    (hwindow : X < a * m ∧ a * m ≤ 2 * X) :
    X < n ∧ n ≤ 2 * δ * X := by
  have h1 := mul_le_mul_of_nonneg_right hl hm
  have h2 := mul_le_mul_of_nonneg_right hu hm
  have h3 := mul_le_mul_of_nonneg_left hwindow.2 (show 0 ≤ δ by linarith)
  constructor <;> nlinarith

lemma mrt_coarse_window_interior {X δ a p m n : ℝ} (hδ : 1 ≤ δ)
    (hm : 0 ≤ m) (hl : a ≤ p) (hu : p ≤ δ * a) (hn : p * m = n)
    (hinterior : δ * X < n ∧ n ≤ 2 * X) :
    X < a * m ∧ a * m ≤ 2 * X := by
  have h1 := mul_le_mul_of_nonneg_right hl hm
  have h2 := mul_le_mul_of_nonneg_right hu hm
  have hd : 0 < δ := by linarith
  constructor
  · apply (mul_lt_mul_iff_right₀ hd).mp
    nlinarith
  · linarith

lemma mrt_coarse_weight_zero (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hn : ¬((N : ℝ) < n ∧ (n : ℝ) ≤ 2 * δ * N)) :
    mrtCoarseRamareWeight P L N n = 0 := by
  apply sum_eq_zero
  intro p hp
  by_cases hpn : p ∣ n
  · have hmul : (p : ℝ) * (n / p : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hpn
    have hw : ¬((N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N) := by
      intro h
      exact hn (mrt_coarse_window_support hδ (Nat.cast_nonneg _) (hL p hp).1
        (hL p hp).2 hmul h)
    rw [if_neg hw, mul_zero]
  · simp only [mrtRamareWeight, if_neg hpn, zero_mul]

lemma mrt_coarse_weight_interior (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hn : δ * N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N) :
    mrtCoarseRamareWeight P L N n = ∑ p ∈ P, mrtRamareWeight P n p := by
  apply sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · have hmul : (p : ℝ) * (n / p : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hpn
    have hw := mrt_coarse_window_interior hδ (Nat.cast_nonneg _) (hL p hp).1
      (hL p hp).2 hmul hn
    rw [if_pos hw, mul_one]
  · simp only [mrtRamareWeight, if_neg hpn, zero_mul]


lemma mrt_coarse_boundary_abs (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (L : ℕ → ℝ) (N n : ℕ) : |mrtCoarseBoundaryCoefficient P L N n| ≤ 1 := by
  have hc0 := mrtCoarseRamareWeight_nonneg P L N n
  have hc1 := mrt_coarse_weight_le_one P hP L N n
  have hr0 : 0 ≤ ∑ p ∈ P, mrtRamareWeight P n p :=
    sum_nonneg fun p _ => mrtRamareWeight_nonneg P n p
  have hr1 := mrt_ramare_weight_sum_le_one P hP n
  unfold mrtCoarseBoundaryCoefficient
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

theorem mrt_coarse_boundary_support (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hn : n ∉ mrtBoundarySet N δ) : mrtCoarseBoundaryCoefficient P L N n = 0 := by
  have hnot := mt (mrt_mem_boundary_iff N n hδ).mpr hn
  unfold mrtCoarseBoundaryCoefficient
  by_cases hwindow : N < n ∧ n ≤ 2 * N
  · have hi : δ * N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
      constructor
      · by_contra h
        exact hnot (Or.inl ⟨hwindow.1, le_of_not_gt h⟩)
      · exact_mod_cast hwindow.2
    rw [if_pos hwindow, mrt_coarse_weight_interior P L N n hδ hL hi, sub_self]
  · have ho : ¬((N : ℝ) < n ∧ (n : ℝ) ≤ 2 * δ * N) := by
      rintro ⟨hnN, hnU⟩
      have hnN' : N < n := by exact_mod_cast hnN
      have hn2 : 2 * N < n := by omega
      apply hnot
      right
      refine ⟨hn2, ?_⟩
      convert (preTransparency := .instances) hnU using 1
      push_cast
      ring
    rw [if_neg hwindow, mrt_coarse_weight_zero P L N n hδ hL ho, sub_self]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCoarseMean
namespace OAI

/-! The literal coarse-bin polynomial differs from the supported dyadic
polynomial by the prime-square correction and the two short boundary
strips.  Both errors are estimated before any sum over prime bins. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical




lemma mrt_dyadic_polynomial_extend (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    mrtDyadicPolynomial b N t =
      mrtExponentialPolynomial (Ioc 0 (4 * N))
        (fun n => (if N < n ∧ n ≤ 2 * N then b n else 0) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  calc
    _ = ∑ n ∈ Ioc N (2 * N),
        ((if N < n ∧ n ≤ 2 * N then b n else 0) / (n : ℂ)) *
          Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
      apply sum_congr rfl
      intro n hn
      rw [if_pos (mem_Ioc.mp hn)]
    _ = _ := by
      apply sum_subset
      · intro n hn
        have hn' := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨by omega, by omega⟩
      · intro n _ hn
        simp only [mem_Ioc] at hn
        rw [if_neg hn, zero_div, zero_mul]

/-- Exact boundary identity, with the original and coarse polynomials
both retaining their actual numerical coefficients. -/
theorem mrt_coarse_boundary_identity (P : Finset ℕ) (L : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ) (t : ℝ) :
    mrtDyadicPolynomial (mrtWeightedRamareCoefficient P F) N t -
        mrtCoarsePolynomial P L N F t =
      mrtCoarseBoundaryPolynomial P L N δ F t := by
  rw [mrt_dyadic_polynomial_extend]
  unfold mrtCoarsePolynomial mrtCoarseBoundaryPolynomial mrtExponentialPolynomial
  rw [← sum_sub_distrib]
  calc
    _ = ∑ n ∈ Ioc 0 (4 * N),
        (F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ) / (n : ℂ)) *
          Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
      apply sum_congr rfl
      intro n _
      unfold mrtWeightedRamareCoefficient mrtCoarseBoundaryCoefficient
      by_cases hn : N < n ∧ n ≤ 2 * N
      · simp only [if_pos hn, Complex.ofReal_sub]
        ring
      · simp only [if_neg hn, Complex.ofReal_sub, Complex.ofReal_zero]
        ring
    _ = _ := by
      symm
      apply sum_subset
      · intro n hn
        obtain ⟨hn1, hn2⟩ := mrt_boundary_range hN hδ2 hn
        exact mem_Ioc.mpr ⟨by omega, hn2⟩
      · intro n _ hn
        dsimp only
        rw [mrt_coarse_boundary_support P L N n hδ hL hn,
          Complex.ofReal_zero, mul_zero, zero_div, zero_mul]

lemma mrt_coarse_boundary_coefficient_norm (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) (N : ℕ)
    (F : ℕ → ℂ) (hF : OneBounded F) {n : ℕ} (hn : 0 < n) :
    ‖F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (hF n hn) (mrt_coarse_boundary_abs P hP L N n)
    (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem mrt_coarse_boundary_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (F : ℕ → ℂ) (hF : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtCoarseBoundaryPolynomial P L N δ F t‖ ^ 2) ≤
      96 * Real.exp 1 * (T / (N : ℝ) + 1) * (δ - 1) := by
  apply mrt_boundary_mean_square
    (fun n => F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ)) hN hδ hδ2 _ hT
  intro n hn
  exact mrt_coarse_boundary_coefficient_norm P hP L N F hF
    (hN.trans (mrt_boundary_range hN hδ2 hn).1)

lemma mrt_weighted_ramare_sum (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    (∑ p ∈ P, if p ∣ n then
      F n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) =
      mrtWeightedRamareCoefficient P F n := by
  unfold mrtWeightedRamareCoefficient
  rw [Complex.ofReal_sum, mul_sum]
  apply sum_congr rfl
  intro p _
  unfold mrtRamareWeight
  by_cases hp : p ∣ n
  · simp only [hp, ite_true, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast]
    ring
  · simp only [hp, ite_false, Complex.ofReal_zero, mul_zero]


lemma mrt_supported_ramare_split (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    mrtSupportedCoefficient P F n =
      mrtRamareCorrection P F n + mrtWeightedRamareCoefficient P F n := by
  unfold mrtSupportedCoefficient mrtRamareCorrection
  rw [mrt_weighted_ramare_sum]
  ring

lemma mrt_dyadic_polynomial_add (a b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    mrtDyadicPolynomial (fun n => a n + b n) N t =
      mrtDyadicPolynomial a N t + mrtDyadicPolynomial b N t := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  simp only [add_div, add_mul, sum_add_distrib]

theorem mrt_coarse_error_identity (P : Finset ℕ) (L : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ) (t : ℝ) :
    mrtDyadicPolynomial (mrtSupportedCoefficient P F) N t -
        mrtCoarsePolynomial P L N F t =
      mrtDyadicPolynomial (mrtRamareCorrection P F) N t +
        mrtCoarseBoundaryPolynomial P L N δ F t := by
  have hs : mrtSupportedCoefficient P F =
      fun n => mrtRamareCorrection P F n + mrtWeightedRamareCoefficient P F n :=
    funext (mrt_supported_ramare_split P F)
  rw [hs, mrt_dyadic_polynomial_add]
  rw [← mrt_coarse_boundary_identity P L hN hδ hδ2 hL F t]
  ring

/-- Coarse-bin decoupling costs the reciprocal square mass and the bin
width.  There is no loss depending on the number of bins. -/
theorem mrt_coarse_error_mean_square (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ) (hF : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtSupportedCoefficient P F) N t -
      mrtCoarsePolynomial P L N F t‖ ^ 2) ≤
      192 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
  let A := mrtDyadicPolynomial (mrtRamareCorrection P F) N
  let B := mrtCoarseBoundaryPolynomial P L N δ F
  have hA : Continuous A := mrtExponentialPolynomial_continuous _ _ _
  have hB : Continuous B := mrtExponentialPolynomial_continuous _ _ _
  have ha : IntervalIntegrable (fun t => ‖A t‖ ^ 2) volume (-T) T :=
    (hA.norm.pow 2).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun t => ‖B t‖ ^ 2) volume (-T) T :=
    (hB.norm.pow 2).intervalIntegrable _ _
  have hab : IntervalIntegrable (fun t => ‖A t + B t‖ ^ 2) volume (-T) T :=
    ((hA.add hB).norm.pow 2).intervalIntegrable _ _
  have hmajor : (∫ t in -T..T, ‖A t + B t‖ ^ 2) ≤
      2 * (∫ t in -T..T, ‖A t‖ ^ 2) + 2 * (∫ t in -T..T, ‖B t‖ ^ 2) := by
    calc
      _ ≤ ∫ t in -T..T, (2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on (by linarith : -T ≤ T) hab
          ((ha.const_mul 2).add (hb.const_mul 2))
        intro t _
        have hh := norm_add_le (A t) (B t)
        nlinarith [sq_nonneg (‖A t‖ - ‖B t‖), norm_nonneg (A t + B t),
          norm_nonneg (A t), norm_nonneg (B t)]
      _ = _ := by
        rw [intervalIntegral.integral_add (ha.const_mul 2) (hb.const_mul 2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [mrt_coarse_error_identity P L hN hδ hδ2 hL F]
  change (∫ t in -T..T, ‖A t + B t‖ ^ 2) ≤ _
  apply hmajor.trans
  have hma := mrt_ramare_correction_mean_square P hP F hF hN hT
  have hmb := mrt_coarse_boundary_mean P hP L hN hδ hδ2 F hF hT
  change (∫ t in -T..T, ‖A t‖ ^ 2) ≤ _ at hma
  change (∫ t in -T..T, ‖B t‖ ^ 2) ≤ _ at hmb
  have hc : 0 ≤ Real.exp 1 * (T / (N : ℝ) + 1) := by positivity
  have hs : 0 ≤ (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
      (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 := by positivity
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCoarseFactorization
namespace OAI

/-! Exact factorization of the coarse Ramaré polynomial into short prime
polynomials and cofactor polynomials with fixed multiplicative windows. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma mrt_dirichlet_atom_mul_of_product (F A B : ℕ → ℂ)
    {p m : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hF : F (p * m) = A p * B m) (t : ℝ) :
    mrtDirichletAtom F (p * m) t =
      mrtDirichletAtom A p t * mrtDirichletAtom B m t := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : Complex.exp (((-Real.log ((p * m : ℕ) : ℝ)) * t : ℝ) * Complex.I) =
      Complex.exp (((-Real.log (p : ℝ)) * t : ℝ) * Complex.I) *
        Complex.exp (((-Real.log (m : ℝ)) * t : ℝ) * Complex.I) := by
    rw [Nat.cast_mul, Real.log_mul hpR.ne' hmR.ne', neg_add, add_mul,
      Complex.ofReal_add, add_mul, Complex.exp_add]
  unfold mrtDirichletAtom
  rw [hF, Nat.cast_mul, he]
  ring


lemma mrt_coarse_polynomial_prime_sum (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (F : ℕ → ℂ) (t : ℝ) :
    mrtCoarsePolynomial P L N F t =
      ∑ p ∈ P, ∑ n ∈ Icc 1 (4 * N),
        if p ∣ n then
          if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
            mrtDirichletAtom F n t /
              ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
          else 0
        else 0 := by
  unfold mrtCoarsePolynomial mrtExponentialPolynomial mrtCoarseRamareWeight
  simp only [Complex.ofReal_sum, mul_sum, sum_div, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [show Ioc 0 (4 * N) = Icc 1 (4 * N) by ext n; simp only [mem_Ioc, mem_Icc]; omega]
  apply sum_congr rfl
  intro n _
  unfold mrtRamareWeight mrtDirichletAtom
  by_cases hp : p ∣ n
  · by_cases hw : (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N
    · simp only [if_pos hp, if_pos hw, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
      ring
    · simp only [if_pos hp, if_neg hw, mul_zero, Complex.ofReal_zero,
        zero_mul, zero_div]
  · simp only [if_neg hp, zero_mul, Complex.ofReal_zero, mul_zero, zero_div]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalFactors
namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators















/-- Dividing out a number smaller than all the selected primes does not
change membership in the typical-factorization set. -/
theorem mrtTypical_mul_of_avoids {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime) {d : ℕ}
    (hd : mrtPrimeAvoids (J.biUnion P) d) (n : ℕ) :
    mrtTypical J P (d * n) ↔ mrtTypical J P n := by
  constructor
  · intro h j hj
    obtain ⟨p, hp, hpdn⟩ := h j hj
    refine ⟨p, hp, ?_⟩
    exact ((hP j hj p hp).dvd_mul.mp hpdn).resolve_left
      (hd p (mem_biUnion.mpr ⟨j, hj, hp⟩))
  · intro h j hj
    obtain ⟨p, hp, hpn⟩ := h j hj
    exact ⟨p, hp, dvd_mul_of_dvd_right hpn d⟩



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalRamare
namespace OAI

/-! Ramaré factorization on the actual typical-factorization set.  Removing
one selected prime band leaves exactly the remaining-band condition; the
prime-square correction and its bound are retained. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators

lemma mrtTypical_count_pos {ι : Type*} {J : Finset ι} {P : ι → Finset ℕ}
    {j : ι} (hj : j ∈ J) {n : ℕ} (hn : mrtTypical J P n) :
    0 < finitePrimeDivisorCount (P j) n := by
  obtain ⟨p, hp, hpn⟩ := hn j hj
  exact finitePrimeDivisorCount_pos_of_mem hp hpn

lemma mrtTypical_prime_mul {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    {p : ℕ} (hp : p ∈ P j) (m : ℕ) :
    mrtTypical J P (p * m) ↔ mrtTypical (J.erase j) P m := by
  have hnot (i : ι) (hi : i ∈ J.erase j) : p ∉ P i := by
    intro hpi
    exact Finset.disjoint_left.mp (hdis (mem_erase.mp hi).2 hj (mem_erase.mp hi).1)
      hpi hp
  have hd : mrtPrimeAvoids ((J.erase j).biUnion P) p := by
    intro q hq hqp
    obtain ⟨i, hi, hqi⟩ := mem_biUnion.mp hq
    have he : q = p := (Nat.prime_dvd_prime_iff_eq
      (hP i (mem_erase.mp hi).2 q hqi) (hP j hj p hp)).mp hqp
    exact hnot i hi (he ▸ hqi)
  have hmul := mrtTypical_mul_of_avoids (J.erase j) P
    (fun i hi => hP i (mem_erase.mp hi).2) hd m
  constructor
  · intro h
    apply hmul.mp
    exact fun i hi => h i (mem_erase.mp hi).2
  · intro h i hi
    by_cases hij : i = j
    · subst i
      exact ⟨p, hp, dvd_mul_right p m⟩
    · exact hmul.mpr h i (mem_erase.mpr ⟨hij, hi⟩)

lemma mrtTypical_ramare_supported {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    {j : ι} (hj : j ∈ J) (F : ℕ → ℂ) (n : ℕ) :
    (if finitePrimeDivisorCount (P j) n = 0 then 0 else
      if mrtTypical J P n then F n else 0) =
      if mrtTypical J P n then F n else 0 := by
  by_cases ht : mrtTypical J P n
  · have hpos := mrtTypical_count_pos hj ht
    simp only [ht, ite_true, ne_of_gt hpos, ite_false]
  · simp only [ht, ite_false, ite_self]





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

lemma mrtTypicalCoefficient_supported {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) {j : ι} (hj : j ∈ J) (F : ℕ → ℂ) :
    mrtSupportedCoefficient (P j) (mrtTypicalCoefficient J P F) =
      mrtTypicalCoefficient J P F := by
  funext n
  exact mrtTypical_ramare_supported J P hj F n




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralPrimeError
namespace OAI

/-! The general-multiplicative discrepancy in extracting a prime factor.
It vanishes unless that prime divides the cofactor, and hence has the
same prime-square support as the corrected Ramaré denominator error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrtTypicalCoefficient_prime_mul_coprime {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (hF : Multiplicative F)
    {p : ℕ} (hp : p ∈ P j) {m : ℕ} (hm : 0 < m) (hpm : ¬p ∣ m) :
    mrtTypicalCoefficient J P F (p * m) =
      F p * mrtTypicalCoefficient (J.erase j) P F m := by
  unfold mrtTypicalCoefficient
  rw [mrtTypical_prime_mul J P hP hdis hj hp]
  split_ifs
  · exact hF p m (hP j hj p hp).pos hm ((hP j hj p hp).coprime_iff_not_dvd.mpr hpm)
  · simp


theorem mrt_prime_product_error_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (active : ℕ → ℕ → Prop) (C A B : ℕ → ℂ)
    (hC : OneBounded C) (hA : OneBounded A) (hB : OneBounded B)
    (hproduct : ∀ p ∈ P, ∀ m, 0 < m → ¬p ∣ m → C (p * m) = A p * B m)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtPrimeProductError P active C A B n‖ ≤ 2 * mrtPrimeSquareCount P n := by
  unfold mrtPrimeProductError
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, if p ^ 2 ∣ n then (2 : ℝ) else 0 := by
      apply sum_le_sum
      intro p hp
      by_cases hgate : p ∣ n ∧ active p n
      · rw [if_pos hgate]
        have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hgate.1) (hP p hp).pos
        by_cases hsquare : p ^ 2 ∣ n
        · rw [if_pos hsquare, norm_div, Complex.norm_natCast]
          have hc : ‖C n - A p * B (n / p)‖ ≤ 2 := by
            apply (norm_sub_le _ _).trans
            rw [norm_mul]
            have hab := mul_le_mul (hA p (hP p hp).pos) (hB (n / p) hm)
              (norm_nonneg _) zero_le_one
            nlinarith [hC n hn]
          calc
            _ ≤ 2 / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hc (by positivity)
            _ ≤ 2 := div_le_self (by norm_num) (by norm_num)
        · have hnot : ¬p ∣ n / p := by
            intro hd
            apply hsquare
            simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hgate.1).mp hd
          have he : C n = A p * B (n / p) := by
            calc
              C n = C (p * (n / p)) := congrArg C (Nat.mul_div_cancel' hgate.1).symm
              _ = _ := hproduct p hp (n / p) hm hnot
          rw [he, sub_self, zero_div, norm_zero, if_neg hsquare]
      · rw [if_neg hgate, norm_zero]
        split_ifs <;> norm_num
    _ = _ := by
      unfold mrtPrimeSquareCount
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      split_ifs <;> norm_num

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralPrimeMean
namespace OAI

/-! Mean-square control of the general multiplicative prime-extraction
error. The broad coarse window is handled before any sum over bins. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem mrt_prime_square_broad_coefficient_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (4 * N), ‖b n‖ ≤ 2 * mrtPrimeSquareCount P n) :
    (∑ n ∈ Ioc N (4 * N), ‖b n / (n : ℂ)‖ ^ 2) ≤
      (16 / (N : ℝ)) * ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ n ∈ Ioc N (4 * N), ((2 * mrtPrimeSquareCount P n) / (N : ℝ)) ^ 2 := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_natCast]
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div₀ (mul_nonneg (by norm_num) (mrtPrimeSquareCount_nonneg P n))
        (hb n hn) hNr
        (by exact_mod_cast (mem_Ioc.mp hn).1.le)
    _ = (4 * (N : ℝ)⁻¹ ^ 2) * ∑ n ∈ Ioc N (4 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      have he (n : ℕ) : ((2 * mrtPrimeSquareCount P n) / (N : ℝ)) ^ 2 =
          (4 * (N : ℝ)⁻¹ ^ 2) * (mrtPrimeSquareCount P n) ^ 2 := by ring
      simp_rw [he]
      rw [← mul_sum]
    _ ≤ (4 * (N : ℝ)⁻¹ ^ 2) * ∑ n ∈ Icc 1 (4 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      · exact fun _ _ _ => sq_nonneg _
    _ ≤ (4 * (N : ℝ)⁻¹ ^ 2) * ((4 * N : ℕ) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_count_second_moment P hP (4 * N))
        (by positivity)
    _ = _ := by
      push_cast
      field_simp
      ring

/-- A prime-extraction error of size twice the square-divisor count has
an absolute mean-square cost on the complete coarse window. -/
theorem mrt_prime_square_broad_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (4 * N), ‖b n‖ ≤ 2 * mrtPrimeSquareCount P n)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial (Ioc N (4 * N))
      (fun n => b n / (n : ℂ)) (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      512 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := mrt_dirichlet_mean_square_subset (Ioc N (4 * N)) (N := 4 * N)
    (by intro n hn; exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,
      (mem_Ioc.mp hn).2⟩) (fun n => b n / (n : ℂ)) hT
  apply hm.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (4 * N : ℕ)) * ((16 / (N : ℝ)) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_broad_coefficient_mass P hP b hN hb)
        (by positivity)
    _ = 128 * Real.exp 1 * (T / (N : ℝ) + 4) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
      push_cast
      field_simp
      ring
    _ ≤ _ := by
      have hc : 0 ≤ (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 := by positivity
      nlinarith [mul_nonneg (Real.exp_pos 1).le hc,
        mul_nonneg (div_nonneg hT.le hNr.le) (mul_nonneg (Real.exp_pos 1).le hc)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralFactorization
namespace OAI

/-! Exact coarse prime extraction with its prime-square discrepancy.
Only coprime multiplicativity is needed when the discrepancy is bounded. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_prime_cofactor_expansion (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hδ2 : δ ≤ 2) {p : ℕ} (hp : p ∈ P) (hp0 : 0 < p)
    (A B : ℕ → ℂ) (t : ℝ) :
    mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t =
      ∑ n ∈ Icc 1 (4 * N), if p ∣ n then
        if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
          ((A p * B (n / p)) / (n : ℂ) *
            Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I)) /
              ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
        else 0
      else 0 := by
  let F : ℕ → ℂ := fun n => A p * B (n / p)
  let G : ℕ → ℂ := fun n =>
    if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
      mrtDirichletAtom F n t / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
    else 0
  have he := divisibility_positivePrefix G p (4 * N) hp0
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, ite_mul, one_mul, zero_mul] at he
  change _ = ∑ n ∈ Icc 1 (4 * N), if p ∣ n then G n else 0
  rw [he]
  have hrange : Icc 1 (4 * N / p) ⊆ Icc 1 (4 * N) := by
    intro m hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1,
      (mem_Icc.mp hm).2.trans (Nat.div_le_self _ _)⟩
  have hf (m : ℕ) : F (p * m) = A p * B m := by
    dsimp [F]
    rw [Nat.mul_div_cancel_left m hp0]
  have hexpand : (∑ m ∈ Icc 1 (4 * N / p), G (p * m)) =
      ∑ m ∈ Icc 1 (4 * N), G (p * m) := by
    apply sum_subset hrange
    intro m hm hout
    dsimp only [G]
    rw [Nat.mul_div_cancel_left m hp0]
    apply if_neg
    intro hw
    have hpm := (mrt_coarse_window_support hδ (show (0 : ℝ) ≤ m by positivity)
      (hL p hp).1 (hL p hp).2 rfl hw).2
    have hmul : (p : ℝ) * m ≤ (4 * N : ℕ) := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      push_cast
      nlinarith
    have hnat : p * m ≤ 4 * N := by exact_mod_cast hmul
    exact hout (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,
      (Nat.le_div_iff_mul_le hp0).mpr (by simpa only [Nat.mul_comm] using hnat)⟩)
  rw [hexpand]
  unfold mrtCofactorPolynomial
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  dsimp only [G]
  rw [Nat.mul_div_cancel_left m hp0]
  by_cases hw : (N : ℝ) < L p * m ∧ L p * m ≤ 2 * N
  · rw [if_pos hw, if_pos hw,
      mrt_dirichlet_atom_mul_of_product F A B hp0 (mem_Icc.mp hm).1 (hf m)]
    ring
  · simp only [if_neg hw, mul_zero]


lemma mrt_prime_extraction_error_zero (P : Finset ℕ) (L : ℕ → ℝ)
    (hL : ∀ p ∈ P, L p ≤ p) (N : ℕ) (C A B : ℕ → ℂ)
    {n : ℕ} (hn : n ≤ N) : mrtPrimeExtractionError P L N C A B n = 0 := by
  unfold mrtPrimeExtractionError mrtPrimeProductError
  apply sum_eq_zero
  intro p hp
  apply if_neg
  rintro ⟨hd, hlo, _⟩
  have hprod : L p * (n / p : ℕ) ≤ (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (hL p hp) (show (0 : ℝ) ≤ (n / p : ℕ) by positivity)
    simpa only [← Nat.cast_mul, Nat.mul_div_cancel' hd] using hh
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  linarith

/-- The exact polynomial identity precedes all norm estimates and keeps
one discrepancy coefficient per integer, rather than per prime bin. -/
theorem mrt_general_prime_factorization (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) (N : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (C A B : ℕ → ℂ) (t : ℝ) :
    mrtCoarsePolynomial P L N C t -
      (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t) =
      mrtExponentialPolynomial (Ioc N (4 * N))
        (fun n => mrtPrimeExtractionError P L N C A B n / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  have hex : (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t) =
      ∑ p ∈ P, ∑ n ∈ Icc 1 (4 * N), if p ∣ n then
        if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
          ((A p * B (n / p)) / (n : ℂ) *
            Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I)) /
              ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
        else 0
      else 0 := by
    apply sum_congr rfl
    intro p hp
    exact mrt_prime_cofactor_expansion P L N hδ hL hδ2 hp (hP p hp).pos A B t
  rw [mrt_coarse_polynomial_prime_sum, hex, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  rw [sum_comm]
  unfold mrtExponentialPolynomial
  calc
    _ = ∑ n ∈ Icc 1 (4 * N),
        (mrtPrimeExtractionError P L N C A B n / (n : ℂ)) *
          Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
      apply sum_congr rfl
      intro n _
      unfold mrtPrimeExtractionError mrtPrimeProductError
      rw [sum_div, sum_mul]
      apply sum_congr rfl
      intro p _
      by_cases hd : p ∣ n
      · by_cases hw : (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N
        · simp only [hd, hw, ite_true, and_self, mrtDirichletAtom]
          ring
        · simp only [hd, hw, ite_true, ite_false, and_false, sub_self, zero_div, zero_mul]
      · simp only [hd, false_and, ite_false, sub_self, zero_div, zero_mul]
    _ = _ := by
      symm
      apply sum_subset
      · intro n hn
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      · intro n hn hnot
        have hnN : n ≤ N := by
          by_contra h
          exact hnot (mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩)
        dsimp only
        rw [mrt_prime_extraction_error_zero P L (fun p hp => (hL p hp).1) N C A B hnN]
        simp


/-- The coarse prime-product factorization is valid for general
multiplicative coefficients up to the already controlled square error. -/
theorem mrt_general_prime_factorization_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (C A B : ℕ → ℂ) (hC : OneBounded C) (hA : OneBounded A) (hB : OneBounded B)
    (hproduct : ∀ p ∈ P, ∀ m, 0 < m → ¬p ∣ m → C (p * m) = A p * B m)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtCoarsePolynomial P L N C t -
      (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t)‖ ^ 2) ≤
      512 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  simp_rw [mrt_general_prime_factorization P hP L N hδ hδ2 hL C A B]
  apply mrt_prime_square_broad_mean P hP _ hN _ hT
  intro n hn
  exact mrt_prime_product_error_bound P hP _ C A B hC hA hB hproduct
    (hN.trans (mem_Ioc.mp hn).1)

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

lemma mrt_extracted_prime_bins {κ : Type*} [DecidableEq κ]
    (K : Finset κ) (P : Finset ℕ) (bin : ℕ → κ)
    (hbin : ∀ p ∈ P, bin p ∈ K) (lower : κ → ℝ) (N : ℕ)
    (A B : ℕ → ℂ) (t : ℝ) :
    (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (lower (bin p)) t) =
      ∑ k ∈ K,
        mrtExponentialPolynomial (P.filter (fun p => bin p = k))
          (fun p => A p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t *
        mrtCofactorPolynomial P B N (lower k) t := by
  rw [← sum_fiberwise_of_maps_to hbin]
  apply sum_congr rfl
  intro k _
  unfold mrtExponentialPolynomial
  rw [sum_mul]
  apply sum_congr rfl
  intro p hp
  have hbp := (mem_filter.mp hp).2
  simp only [mrtDirichletAtom, hbp]

theorem mrt_typical_general_prime_mean_square {ι : Type*}
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (lower : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower p ≤ p ∧ (p : ℝ) ≤ δ * lower p)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t -
        ∑ p ∈ P j, mrtDirichletAtom F p t *
          mrtCofactorPolynomial (P j) (mrtTypicalCoefficient (J.erase j) P F) N (lower p) t‖ ^ 2) ≤
      1408 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
  let C := mrtTypicalCoefficient J P F
  let B := mrtTypicalCoefficient (J.erase j) P F
  let D := mrtDyadicPolynomial C N
  let G := mrtCoarsePolynomial (P j) lower N C
  let H : ℝ → ℂ := fun t => ∑ p ∈ P j, mrtDirichletAtom F p t *
    mrtCofactorPolynomial (P j) B N (lower p) t
  have hD : Continuous D := mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := mrtExponentialPolynomial_continuous _ _ _
  have hR (p : ℕ) : Continuous (fun t => mrtCofactorPolynomial (P j) B N (lower p) t) :=
    mrtCofactorPolynomial_continuous (P j) B N (lower p)
  have hH : Continuous H := by
    apply continuous_finsetSum
    intro p _
    apply Continuous.mul _ (hR p)
    unfold mrtDirichletAtom
    fun_prop
  have hboundary := mrt_coarse_error_mean_square (P j) (hP j hj) lower
    hN hδ hδ2 hL C (mrtTypicalCoefficient_oneBounded J P F hFb) hT
  rw [mrtTypicalCoefficient_supported J P hj F] at hboundary
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at hboundary
  have hproduct := mrt_general_prime_factorization_mean (P j) (hP j hj) lower hN hδ hδ2 hL
    C F B (mrtTypicalCoefficient_oneBounded J P F hFb) hFb
    (mrtTypicalCoefficient_oneBounded (J.erase j) P F hFb)
    (fun p hp m hm hpm => mrtTypicalCoefficient_prime_mul_coprime J P hP hdis hj F hF hp hm hpm)
    hT
  change (∫ t in -T..T, ‖G t - H t‖ ^ 2) ≤ _ at hproduct
  have hproduct' : (∫ t in -T..T, ‖G t - H t‖ ^ 2) ≤
      512 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
    apply hproduct.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_right (by linarith)
  have hs := mrt_restricted_energy_split (fun t => D t - H t) (fun t => G t - H t)
    (hD.sub hH) (hG.sub hH) hT.le (Set.Subset.refl (Set.Ioc (-T) T))
  have he (t : ℝ) : (D t - H t) - (G t - H t) = D t - G t := by ring
  simp only [he, ← intervalIntegral.integral_of_le (show -T ≤ T by linarith)] at hs
  apply hs.trans
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hboundary (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hproduct' (by norm_num : (0 : ℝ) ≤ 2))
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

/-- The usual cofactor mean square, with its actual length `N/a`.
Neither the number nor the sizes of other prime bands enter the constant. -/
theorem mrt_cofactor_mean_square (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N : ℝ) / a) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtCofactorPolynomial P F N a t‖ ^ 2) ≤
      32 * Real.exp 1 * (T * a / (N : ℝ) + 1) := by
  let m := ⌊(N : ℝ) / a⌋₊
  let n := ⌊(2 * N : ℝ) / a⌋₊
  have ha0 : 0 < a := by linarith
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * a)
    ((le_div_iff₀ ha0).mp hx)
  obtain ⟨hm, hmn, _⟩ := mrt_cofactor_window_ratio N ha0 hx
  change 0 < m at hm
  change m ≤ n at hmn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlower : (N : ℝ) / a ≤ 2 * m := by
    have hfloor := Nat.lt_floor_add_one ((N : ℝ) / a)
    change (N : ℝ) / a < (m : ℝ) + 1 at hfloor
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hNm : (N : ℝ) ≤ 2 * a * m := by
    have hh := (div_le_iff₀ ha0).mp hlower
    nlinarith
  have hnR : (n : ℝ) ≤ 4 * m := by
    have hfloor := Nat.floor_le (show 0 ≤ (2 * N : ℝ) / a by positivity)
    change (n : ℝ) ≤ (2 * N : ℝ) / a at hfloor
    have he : (2 * N : ℝ) / a = 2 * ((N : ℝ) / a) := by ring
    rw [he] at hfloor
    linarith
  have hcoeff := mrt_reciprocal_count_oneBounded P F hF
  have hmass : (∑ k ∈ Ioc m n,
      ‖(F k / ((finitePrimeDivisorCount P k + 1 : ℕ) : ℂ)) / (k : ℂ)‖ ^ 2) ≤
      (m : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ k ∈ Ioc m n, ((k : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro k hk
        have hk0 : 0 < k := hm.trans (mem_Ioc.mp hk).1
        have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
        rw [norm_div, Complex.norm_natCast]
        calc
          _ ≤ (1 / (k : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity)
            (div_le_div_of_nonneg_right (hcoeff k hk0) hkR.le) 2
          _ = _ := by simp
      _ ≤ (m : ℝ)⁻¹ - (n : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hm.ne' hmn
      _ ≤ _ := sub_le_self _ (by positivity)
  have hmean := mrt_dirichlet_mean_square_subset (Ioc m n)
    (N := n) (by intro k hk; exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hk).1; omega,
      (mem_Ioc.mp hk).2⟩)
    (fun k => (F k / ((finitePrimeDivisorCount P k + 1 : ℕ) : ℂ)) / (k : ℂ)) hT
  have hTm : T / (m : ℝ) ≤ 2 * (T * a / (N : ℝ)) := by
    apply (div_le_iff₀ hmR).mpr
    calc
      T = (T * (N : ℝ)) / N := by field_simp
      _ ≤ (T * (2 * a * m)) / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNm hT.le) hNr.le
      _ = (2 * (T * a / (N : ℝ))) * m := by ring
  have hnm : (n : ℝ) / m ≤ 4 := (div_le_iff₀ hmR).mpr hnR
  simp_rw [mrt_cofactor_exponential_polynomial P F N ha]
  change (∫ t in -T..T, ‖mrtExponentialPolynomial (Ioc m n)
    (fun k => (F k / ((finitePrimeDivisorCount P k + 1 : ℕ) : ℂ)) / (k : ℂ))
    (fun k => -Real.log (k : ℝ)) t‖ ^ 2) ≤ _
  apply hmean.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (n : ℝ)) * (m : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 8 * Real.exp 1 * (T / (m : ℝ) + (n : ℝ) / m) := by ring
    _ ≤ 8 * Real.exp 1 * (2 * (T * a / (N : ℝ)) + 4) :=
      mul_le_mul_of_nonneg_left (add_le_add hTm hnm) (by positivity)
    _ ≤ _ := by
      have hp : 0 ≤ Real.exp 1 * (T * a / (N : ℝ)) := by positivity
      nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralSmallEnergy
namespace OAI

/-! The first-small-band energy bound for ordinary multiplicative
functions, including the explicit prime-square extraction error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem mrt_general_typical_small_prime_energy_oai {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (hlow : ∀ k ∈ K, 1 ≤ lower k) (hupper : ∀ k ∈ K, 2 ≤ (N : ℝ) / lower k)
    (F : ℕ → ℂ)
    (hF : Multiplicative F)
    (hFb : OneBounded F) {T : ℝ} (hT : 0 < T)
    (E : Set ℝ) (hE : E ⊆ Set.Ioc (-T) T) (A : κ → ℝ)
    (hsmall : ∀ k ∈ K, ∀ t ∈ E,
      ‖mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
        (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖ ≤ A k) :
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      2816 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) +
      64 * Real.exp 1 * (K.card : ℝ) *
        ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1) := by
  let B := mrtTypicalCoefficient (J.erase j) P F
  let Q : κ → ℝ → ℂ := fun k =>
    mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
      (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ))
  let R : κ → ℝ → ℂ := fun k => mrtCofactorPolynomial (P j) B N (lower k)
  let D := mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N
  let G : ℝ → ℂ := fun t => ∑ k ∈ K, Q k t * R k t
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded _ _ _ hFb
  have hR (k : κ) (_hk : k ∈ K) : Continuous (R k) :=
    mrtCofactorPolynomial_continuous (P j) B N (lower k)
  have hD : Continuous D := mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := continuous_finsetSum K (fun k hk =>
    (mrtExponentialPolynomial_continuous _ _ _).mul (hR k hk))
  have hg := mrt_restricted_product_sum_energy K Q R hR A hT.le hE hsmall
  have hg' : (∫ t in E, ‖G t‖ ^ 2) ≤
      32 * Real.exp 1 * (K.card : ℝ) *
        ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1) := by
    change (∫ t in E, ‖∑ k ∈ K, Q k t * R k t‖ ^ 2) ≤ _
    apply hg.trans
    calc
      _ ≤ (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
          (32 * Real.exp 1 * (T * lower k / (N : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (mrt_cofactor_mean_square (P j) B hB N (hlow k hk) (hupper k hk) hT)
          (sq_nonneg _)
      _ = _ := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro k _
        ring
  have herr := mrt_typical_general_prime_mean_square J P hP hdis hj
    (fun p => lower (bin p)) hN hδ hδ2 hL F hF hFb hT
  simp_rw [mrt_extracted_prime_bins K (P j) bin hbin lower N F
    (mrtTypicalCoefficient (J.erase j) P F)] at herr
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at herr
  apply (mrt_restricted_energy_split D G hD hG hT.le hE).trans
  calc
    _ ≤ 2 * (1408 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1))) +
        2 * (32 * Real.exp 1 * (K.card : ℝ) *
          ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num))
        (mul_le_mul_of_nonneg_left hg' (by norm_num))
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_general_typical_small_prime_energy_oai := @OAI.TwoPointCorrelations.mrt_general_typical_small_prime_energy_oai
