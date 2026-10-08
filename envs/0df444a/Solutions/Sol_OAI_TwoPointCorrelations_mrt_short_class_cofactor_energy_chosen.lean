-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_short_class_cofactor_energy_chosen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:37:11.742014+00:00
-- url     : https://prove2.me/submissions/0e811a8e-8bf0-4373-a5b8-748d89181ce5

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTEulerProducts
namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.ComplexConjugate

lemma mrt_local_euler_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - z)⁻¹‖ ≤ Real.exp (z.re + ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hnz : 1 - z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp only [he, norm_one] at hz1
    exact lt_irrefl _ hz1
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)).mpr
    linarith
  have hrem : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hre : (Complex.log (1 - z)⁻¹).re ≤ z.re + ‖z‖ ^ 2 := by
    have h := (Complex.re_le_norm (Complex.log (1 - z)⁻¹ - z)).trans hrem
    rw [Complex.sub_re] at h
    linarith
  calc
    _ = Real.exp (Complex.log (1 - z)⁻¹).re := by
      rw [← Complex.norm_exp, Complex.exp_log (inv_ne_zero hnz)]
    _ ≤ _ := Real.exp_le_exp.mpr hre








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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDivisorPairs
namespace OAI

/-! The divisor-square estimate in the mixed prime/cofactor moment.
The map `(d,e) ↦ (gcd(d,e), d/gcd(d,e), e/gcd(d,e))` bounds a pair of
supported divisors by three supported factors whose product divides the
integer. Summing the divisibility tests gives a finite Euler majorant. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mrt_gcd_triple_left (v : ℕ × ℕ) :
    (mrtGcdTriple v).1 * (mrtGcdTriple v).2.1 = v.1 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

lemma mrt_gcd_triple_right (v : ℕ × ℕ) :
    (mrtGcdTriple v).1 * (mrtGcdTriple v).2.2 = v.2 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

lemma mrt_gcd_triple_injective : Function.Injective mrtGcdTriple := by
  intro v w h
  apply Prod.ext
  · rw [← mrt_gcd_triple_left v, ← mrt_gcd_triple_left w, h]
  · rw [← mrt_gcd_triple_right v, ← mrt_gcd_triple_right w, h]

lemma mrt_gcd_triple_product {d e : ℕ} (hd : 0 < d) :
    (mrtGcdTriple (d, e)).1 *
      ((mrtGcdTriple (d, e)).2.1 * (mrtGcdTriple (d, e)).2.2) = Nat.lcm d e := by
  change Nat.gcd d e * (d / Nat.gcd d e * (e / Nat.gcd d e)) = _
  apply Nat.eq_of_mul_eq_mul_left (Nat.gcd_pos_of_pos_left e hd)
  calc
    _ = (Nat.gcd d e * (d / Nat.gcd d e)) *
        (Nat.gcd d e * (e / Nat.gcd d e)) := by ring
    _ = d * e := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
    _ = Nat.gcd d e * Nat.lcm d e := (Nat.gcd_mul_lcm d e).symm

/-- A finite divisor-closed positive set suffices; no asymptotic sieve
or mean-value theorem is hidden in the combinatorial estimate. -/
theorem mrt_divisor_pair_card (S : Finset ℕ)
    (hS : ∀ d ∈ S, 0 < d)
    (hclosed : ∀ d ∈ S, ∀ e : ℕ, 0 < e → e ∣ d → e ∈ S) (n : ℕ) :
    ((S.filter (fun d => d ∣ n)).card) ^ 2 ≤
      ((S ×ˢ (S ×ˢ S)).filter (fun v => v.1 * (v.2.1 * v.2.2) ∣ n)).card := by
  let D := S.filter (fun d => d ∣ n)
  have hm : ∀ v ∈ D ×ˢ D,
      mrtGcdTriple v ∈ (S ×ˢ (S ×ˢ S)).filter
        (fun w => w.1 * (w.2.1 * w.2.2) ∣ n) := by
    rintro ⟨d, e⟩ hv
    obtain ⟨hd, he⟩ := mem_product.mp hv
    obtain ⟨hdS, hdn⟩ := mem_filter.mp hd
    obtain ⟨heS, hen⟩ := mem_filter.mp he
    have hd0 := hS d hdS
    have he0 := hS e heS
    have hg0 := Nat.gcd_pos_of_pos_left e hd0
    have hgd := Nat.gcd_dvd_left d e
    have hge := Nat.gcd_dvd_right d e
    have hqd : 0 < d / Nat.gcd d e := Nat.div_pos (Nat.le_of_dvd hd0 hgd) hg0
    have hqe : 0 < e / Nat.gcd d e := Nat.div_pos (Nat.le_of_dvd he0 hge) hg0
    apply mem_filter.mpr
    constructor
    · exact mem_product.mpr ⟨hclosed d hdS _ hg0 hgd, mem_product.mpr
        ⟨hclosed d hdS _ hqd (Nat.div_dvd_of_dvd hgd),
          hclosed e heS _ hqe (Nat.div_dvd_of_dvd hge)⟩⟩
    · rw [mrt_gcd_triple_product hd0]
      exact Nat.lcm_dvd hdn hen
  have hc := card_le_card_of_injOn mrtGcdTriple hm
    (fun _ _ _ _ h => mrt_gcd_triple_injective h)
  simpa only [card_product, pow_two] using hc

theorem mrt_divisor_count_second_moment (S : Finset ℕ)
    (hS : ∀ d ∈ S, 0 < d)
    (hclosed : ∀ d ∈ S, ∀ e : ℕ, 0 < e → e ∣ d → e ∈ S) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((S.filter (fun d => d ∣ n)).card : ℝ) ^ 2) ≤
      (N : ℝ) * (∑ d ∈ S, 1 / (d : ℝ)) ^ 3 := by
  let K := S ×ˢ (S ×ˢ S)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ v ∈ K,
        if v.1 * (v.2.1 * v.2.2) ∣ n then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro n _
      have hc := mrt_divisor_pair_card S hS hclosed n
      have hcR : ((S.filter (fun d => d ∣ n)).card : ℝ) ^ 2 ≤
          (((S ×ˢ (S ×ˢ S)).filter
            (fun v => v.1 * (v.2.1 * v.2.2) ∣ n)).card : ℝ) := by exact_mod_cast hc
      simpa only [sum_boole] using hcR
    _ = ∑ v ∈ K, ∑ n ∈ Icc 1 N,
        if v.1 * (v.2.1 * v.2.2) ∣ n then (1 : ℝ) else 0 := sum_comm
    _ ≤ ∑ v ∈ K, (N : ℝ) / (v.1 * (v.2.1 * v.2.2) : ℕ) := by
      apply sum_le_sum
      intro v hv
      obtain ⟨h1, h23⟩ := mem_product.mp hv
      obtain ⟨h2, h3⟩ := mem_product.mp h23
      rw [mrt_count_multiples (Nat.mul_pos (hS _ h1) (Nat.mul_pos (hS _ h2) (hS _ h3)))]
      exact Nat.cast_div_le
    _ = (N : ℝ) * (∑ d ∈ S, 1 / (d : ℝ)) ^ 3 := by
      simp only [K, sum_product, Nat.cast_mul, ← div_div]
      simp_rw [div_eq_mul_inv]
      simp only [← mul_sum, ← sum_mul]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFactoredReciprocal
namespace OAI

/-! Finite reciprocal mass of integers supported on a prime band. Together
with the gcd-triple injection this supplies the divisor-square mean bound
in MR's mixed prime/cofactor moment without an additional sieve input. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mrtFactoredUpTo_pos (P : Finset ℕ) (N : ℕ)
    {d : ℕ} (hd : d ∈ mrtFactoredUpTo P N) : 0 < d :=
  (mem_Icc.mp (mem_filter.mp hd).1).1

lemma mrtFactoredUpTo_divisor_closed (P : Finset ℕ) (N : ℕ)
    {d : ℕ} (hd : d ∈ mrtFactoredUpTo P N)
    {e : ℕ} (he : 0 < e) (hed : e ∣ d) : e ∈ mrtFactoredUpTo P N := by
  obtain ⟨hdN, hdP⟩ := mem_filter.mp hd
  exact mem_filter.mpr ⟨mem_Icc.mpr
    ⟨he, (Nat.le_of_dvd (mem_Icc.mp hdN).1 hed).trans (mem_Icc.mp hdN).2⟩,
    Nat.mem_factoredNumbers_of_dvd hdP hed⟩

lemma mrt_reciprocal_prime_power_series {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => (1 : ℝ) / (p ^ k : ℕ)) (1 - (1 : ℝ) / p)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
  simpa only [Nat.cast_pow, one_div, inv_pow] using
    hasSum_geometric_of_lt_one (by positivity : 0 ≤ (p : ℝ)⁻¹) hi

lemma mrt_reciprocal_prime_power_norm {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => ‖(1 : ℝ) / (p ^ k : ℕ)‖) := by
  have he (k : ℕ) : ‖(1 : ℝ) / (p ^ k : ℕ)‖ = 1 / (p ^ k : ℕ) :=
    Real.norm_of_nonneg (by positivity)
  simpa only [he] using (mrt_reciprocal_prime_power_series hp).summable

lemma mrt_factored_reciprocal_series (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers P => (1 : ℝ) / (n.val : ℕ))
      (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) := by
  have h1 : (1 : ℝ) / (1 : ℕ) = 1 := by norm_num
  have hm {m n : ℕ} (_h : m.Coprime n) :
      (1 : ℝ) / (m * n : ℕ) = (1 / (m : ℝ)) * (1 / (n : ℝ)) := by
    simp only [Nat.cast_mul, one_div, mul_inv_rev]
    ring
  obtain ⟨_, he⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (1 : ℝ) / n) h1 (fun {_ _} h => hm h)
    (fun {_} h => mrt_reciprocal_prime_power_norm h) P
  have hf : P.filter Nat.Prime = P := filter_true_of_mem hP
  rw [hf] at he
  have hprod : (∏ p ∈ P, ∑' k : ℕ, (1 : ℝ) / (p ^ k : ℕ)) =
      ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ :=
    prod_congr rfl (fun p hp => (mrt_reciprocal_prime_power_series (hP p hp)).tsum_eq)
  exact hprod ▸ he

theorem mrt_factored_reciprocal_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ d ∈ mrtFactoredUpTo P N, 1 / (d : ℝ)) ≤
      ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := by
  have hi : HasSum ((Nat.factoredNumbers P).indicator (fun n : ℕ => (1 : ℝ) / n))
      (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) :=
    (hasSum_subtype_iff_indicator (s := Nat.factoredNumbers P)
      (f := fun n : ℕ => (1 : ℝ) / n)).mp (mrt_factored_reciprocal_series P hP)
  rw [← hi.tsum_eq]
  calc
    _ = ∑ d ∈ mrtFactoredUpTo P N,
        (Nat.factoredNumbers P).indicator (fun n : ℕ => (1 : ℝ) / n) d := by
      apply sum_congr rfl
      intro d hd
      exact (Set.indicator_of_mem (mem_filter.mp hd).2 (fun n : ℕ => (1 : ℝ) / n)).symm
    _ ≤ _ := hi.summable.sum_le_tsum _ (fun d _ =>
      Set.indicator_nonneg (fun n _ => by positivity) d)


lemma mrt_prime_reciprocal_euler_bound {p : ℕ} (hp : p.Prime) :
    (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hnon : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hhalf : (1 : ℝ) / p ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hp2
  have hz : ‖(((1 : ℝ) / p : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnon] using hhalf
  have he := mrt_local_euler_bound hz
  have hpos : 0 < 1 - (1 : ℝ) / p := by linarith
  have hn : ‖(1 - (((1 : ℝ) / p : ℝ) : ℂ))⁻¹‖ = (1 - (1 : ℝ) / p)⁻¹ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (1 - (1 : ℝ) / p)⁻¹)]
  simpa only [hn, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnon] using he


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedCoefficients
namespace OAI

/-! Coefficients of a prime-polynomial power times a cofactor polynomial.
The cofactor may carry arbitrary bounded masks. Unique factorization costs
only the prime-tuple factorial; the remaining multiplicity is the literal
number of supported divisors, whose second moment was proved separately. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_prime_tuple_factored {r : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (v : Fin r → ℕ)
    (hv : v ∈ Fintype.piFinset (fun _ : Fin r => P)) :
    (∏ i, v i) ∈ Nat.factoredNumbers P := by
  apply Nat.mem_factoredNumbers'.mpr
  intro p hp hdiv
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff v).mp hdiv
  have hvi := Fintype.mem_piFinset.mp hv i
  have he := (Nat.prime_dvd_prime_iff_eq hp (hP _ hvi)).mp hi
  exact he.symm ▸ hvi


theorem mrt_mixed_prime_fiber_card (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ) {n U : ℕ} (hn : 0 < n) (hnU : n ≤ U) :
    (mrtMixedPrimeFiber P M r n).card ≤ r.factorial *
      (((mrtFactoredUpTo P U).filter (fun d => d ∣ n)).card) := by
  let V := Fintype.piFinset (fun _ : Fin r => P)
  let S := mrtMixedPrimeFiber P M r n
  let D := (mrtFactoredUpTo P U).filter (fun d => d ∣ n)
  have htuple (v : Fin r → ℕ) (hv : v ∈ V) : 0 < ∏ i, v i :=
    prod_pos (fun i _ => (hP _ (Fintype.mem_piFinset.mp hv i)).pos)
  have hmap : ∀ v ∈ S, (∏ i, v.1 i) ∈ D := by
    intro v hv
    obtain ⟨hvm, hprod⟩ := mem_filter.mp hv
    obtain ⟨hvP, _⟩ := mem_product.mp hvm
    have hd : (∏ i, v.1 i) ∣ n := hprod ▸ dvd_mul_right _ _
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr
      ⟨htuple _ hvP, (Nat.le_of_dvd hn hd).trans hnU⟩,
      mrt_prime_tuple_factored P hP v.1 hvP⟩, hd⟩
  have hfiber (d : ℕ) : (S.filter (fun v => (∏ i, v.1 i) = d)).card ≤ r.factorial := by
    apply le_trans (card_le_card_of_injOn Prod.fst ?_ ?_)
      (mrt_prime_product_fiber_card V (fun v hv i =>
        hP _ (Fintype.mem_piFinset.mp hv i)) d)
    · intro v hv
      obtain ⟨hvS, hvd⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨(mem_product.mp (mem_filter.mp hvS).1).1, hvd⟩
    · intro v hv w hw he
      obtain ⟨hvS, _⟩ := mem_filter.mp hv
      obtain ⟨hwS, _⟩ := mem_filter.mp hw
      have hvp := (mem_filter.mp hvS).2
      have hwp := (mem_filter.mp hwS).2
      apply Prod.ext he
      apply Nat.eq_of_mul_eq_mul_left
        (htuple v.1 (mem_product.mp (mem_filter.mp hvS).1).1)
      calc
        _ = n := hvp
        _ = _ := by rw [he]; exact hwp.symm
  have hcount : (∑ d ∈ D, (S.filter (fun v => (∏ i, v.1 i) = d)).card) = S.card := by
    simpa using (sum_fiberwise_of_maps_to hmap (fun _ => (1 : ℕ)))
  rw [← hcount]
  calc
    _ ≤ ∑ _d ∈ D, r.factorial := sum_le_sum (fun d _ => hfiber d)
    _ = _ := by simp [D, Nat.mul_comm]


theorem mrt_mixed_prime_coefficient_bound (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {n U : ℕ} (hn : 0 < n) (hnU : n ≤ U) :
    ‖mrtMixedPrimeCoefficient P M a b r n‖ ≤ (r.factorial : ℝ) *
      (((mrtFactoredUpTo P U).filter (fun d => d ∣ n)).card : ℝ) := by
  have ht (v : (Fin r → ℕ) × ℕ) (hv : v ∈ mrtMixedPrimeFiber P M r n) :
      ‖(∏ i, a (v.1 i)) * b v.2‖ ≤ 1 := by
    obtain ⟨hvm, _⟩ := mem_filter.mp hv
    obtain ⟨hvP, hvM⟩ := mem_product.mp hvm
    rw [norm_mul, norm_prod]
    have hp : (∏ i, ‖a (v.1 i)‖) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun i _ => ha _ (Fintype.mem_piFinset.mp hvP i))
    exact (mul_le_mul hp (hb _ hvM) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  calc
    _ ≤ ∑ _v ∈ mrtMixedPrimeFiber P M r n, (1 : ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum ht)
    _ = ((mrtMixedPrimeFiber P M r n).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast mrt_mixed_prime_fiber_card P M hP r hn hnU

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortEuler
namespace OAI

/-! An absolute Euler-factor bound on one short prime bin. Counting all
integers in the bin already suffices, so this local mixed-moment constant
requires no additional prime-distribution theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_short_bin_reciprocal_mass (P : Finset ℕ) {Y : ℕ} (hY : 0 < Y)
    (hP : P ⊆ Icc Y (2 * Y)) :
    (∑ p ∈ P, (1 : ℝ) / p) ≤ 2 := by
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hc : P.card ≤ 2 * Y := by
    have hh := card_le_card hP
    rw [Nat.card_Icc] at hh
    omega
  calc
    _ ≤ ∑ _p ∈ P, (1 : ℝ) / Y := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hYR (by exact_mod_cast (mem_Icc.mp (hP hp)).1)
    _ = (P.card : ℝ) / Y := by simp [div_eq_mul_inv]
    _ ≤ 2 := (div_le_iff₀ hYR).mpr (by exact_mod_cast hc)

lemma mrt_short_bin_reciprocal_square_mass (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) {Y : ℕ} (hY : 0 < Y)
    (hP : P ⊆ Icc Y (2 * Y)) :
    (∑ p ∈ P, ((1 : ℝ) / p) ^ 2) ≤ 1 := by
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ p ∈ P, (1 : ℝ) / p := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hmem
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hmem).two_le
      have hi : (1 : ℝ) / p ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) hp2
      nlinarith [show (0 : ℝ) ≤ 1 / (p : ℝ) by positivity]
    _ ≤ (1 / 2 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left (mrt_short_bin_reciprocal_mass P hY hP) (by norm_num)
    _ = 1 := by norm_num

theorem mrt_short_bin_euler_cube (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) {Y : ℕ} (hY : 0 < Y)
    (hP : P ⊆ Icc Y (2 * Y)) :
    (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 ≤ Real.exp 9 := by
  have hprod : (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ≤
      Real.exp (∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hmem
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hmem).two_le
      have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    · exact fun p hmem => mrt_prime_reciprocal_euler_bound (hp p hmem)
  have hn : 0 ≤ ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := by
    apply prod_nonneg
    intro p hmem
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hmem).two_le
    have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    exact inv_nonneg.mpr (by linarith)
  calc
    _ ≤ (Real.exp (∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2))) ^ 3 :=
      pow_le_pow_left₀ hn hprod 3
    _ = Real.exp (3 * ∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2)) := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [sum_add_distrib]
      linarith [mrt_short_bin_reciprocal_mass P hY hP,
        mrt_short_bin_reciprocal_square_mass P hp hY hP]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeightedTail
namespace OAI

/-! Partial summation of the supported-divisor second moment. This keeps
the mixed Dirichlet coefficient square mass proportional to the inverse
lower endpoint, rather than losing the ratio of its endpoints. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_real_prefix_zero_extension (a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range (n + 1), if i = 0 then 0 else a i) = ∑ i ∈ Icc 1 n, a i := by
  rw [Nat.range_succ_eq_Icc_zero, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp only [ite_true, zero_add]
  have he : Ioc 0 n = Icc 1 n := by ext i; simp only [mem_Ioc, mem_Icc]; omega
  rw [he]
  apply sum_congr rfl
  intro i hi
  rw [if_neg (by have := (mem_Icc.mp hi).1; omega)]

lemma mrt_square_reciprocal_partial_sum (a : ℕ → ℝ) {m n : ℕ} (hmn : m < n) :
    (∑ i ∈ Ioc m n, a i / (i : ℝ) ^ 2) =
      (∑ i ∈ Icc 1 n, a i) / (n : ℝ) ^ 2 -
      (∑ i ∈ Icc 1 m, a i) / (m + 1 : ℕ) ^ 2 +
      ∑ i ∈ Ioc m (n - 1), (∑ j ∈ Icc 1 i, a j) *
        (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) := by
  have he := sum_Ioc_by_parts (fun i : ℕ => (1 : ℝ) / (i : ℝ) ^ 2)
    (fun i : ℕ => if i = 0 then 0 else a i) hmn
  simp only [smul_eq_mul, mrt_real_prefix_zero_extension] at he
  have hl : (∑ i ∈ Ioc m n, 1 / (i : ℝ) ^ 2 * (if i = 0 then 0 else a i)) =
      ∑ i ∈ Ioc m n, a i / (i : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro i hi
    rw [if_neg (by have := (mem_Ioc.mp hi).1; omega)]
    ring
  rw [hl] at he
  rw [he]
  have hs : (∑ i ∈ Ioc m (n - 1),
      (1 / (i + 1 : ℕ) ^ 2 - 1 / (i : ℝ) ^ 2) * (∑ j ∈ Icc 1 i, a j)) =
      -(∑ i ∈ Ioc m (n - 1), (∑ j ∈ Icc 1 i, a j) *
        (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

theorem mrt_weighted_square_tail (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {C : ℝ} (hC : 0 ≤ C)
    (hprefix : ∀ n ≤ U, (∑ i ∈ Icc 1 n, a i) ≤ C * n) :
    (∑ i ∈ Ioc L U, a i / (i : ℝ) ^ 2) ≤ 2 * C / L := by
  by_cases heq : L = U
  · subst U
    simp only [Ioc_eq_empty_of_le le_rfl, sum_empty]
    positivity
  have hlt : L < U := lt_of_le_of_ne hLU heq
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hUR : (0 : ℝ) < U := by exact_mod_cast hL.trans_le hLU
  have hgap (i : ℕ) (hi : i ∈ Ioc L (U - 1)) :
      (∑ j ∈ Icc 1 i, a j) * (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) ≤
        2 * C * (1 / (i : ℝ) - 1 / (i + 1 : ℕ)) := by
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hL.trans (mem_Ioc.mp hi).1
    have hiU : i ≤ U := (mem_Ioc.mp hi).2.trans (Nat.sub_le _ _)
    have hnon : 0 ≤ 1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2 := by
      apply sub_nonneg.mpr
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith
    calc
      _ ≤ (C * i) * (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) :=
        mul_le_mul_of_nonneg_right (hprefix i hiU) hnon
      _ ≤ _ := by
        have hg : (i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) ≤
            2 * (1 / (i : ℝ) - 1 / (i + 1 : ℕ)) := by
          push_cast
          field_simp
          nlinarith
        nlinarith
  have htel : (∑ i ∈ Ioc L (U - 1), (1 / (i : ℝ) - 1 / (i + 1 : ℕ))) =
      1 / (L + 1 : ℕ) - 1 / (U : ℝ) := by
    have hset : Ioc L (U - 1) = Ico (L + 1) U := by
      ext i
      simp only [mem_Ioc, mem_Ico]
      omega
    rw [hset]
    calc
      _ = -(∑ i ∈ Ico (L + 1) U, (1 / (i + 1 : ℕ) - 1 / (i : ℝ))) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [sum_Ico_sub (fun i : ℕ => (1 : ℝ) / i) (show L + 1 ≤ U by omega)]
        ring
  rw [mrt_square_reciprocal_partial_sum a hlt]
  have htop : (∑ i ∈ Icc 1 U, a i) / (U : ℝ) ^ 2 ≤ C / U := by
    apply (div_le_div_of_nonneg_right (hprefix U le_rfl) (sq_nonneg _)).trans_eq
    field_simp
  have hbot : 0 ≤ (∑ i ∈ Icc 1 L, a i) / (L + 1 : ℕ) ^ 2 :=
    div_nonneg (sum_nonneg (fun i _ => ha i)) (sq_nonneg _)
  have hsum := sum_le_sum hgap
  rw [← mul_sum, htel] at hsum
  have hn : 0 ≤ C / (U : ℝ) := div_nonneg hC hUR.le
  calc
    _ ≤ C / U + 2 * C * (1 / (L + 1 : ℕ) - 1 / (U : ℝ)) := by linarith
    _ = 2 * C / (L + 1 : ℕ) - C / U := by ring
    _ ≤ 2 * C / (L + 1 : ℕ) := sub_le_self _ hn
    _ ≤ 2 * C / L := div_le_div_of_nonneg_left (by positivity) hLR
      (by exact_mod_cast Nat.le_add_right L 1)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedMoment
namespace OAI

/-! Mean square of the actual mixed prime/cofactor coefficients. The
factorial cost is explicit, while the finite Euler factor depends only on
the preceding short prime band, not the number of typical-set masks. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem mrt_factored_coefficient_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {L U : ℕ}
    (hL : 0 < L) (hLU : L ≤ U) {A : ℝ}
    (hb : ∀ n ∈ Ioc L U, ‖b n‖ ≤ A *
      (((mrtFactoredUpTo P U).filter (fun d => d ∣ n)).card : ℝ)) :
    (∑ n ∈ Ioc L U, ‖b n / (n : ℂ)‖ ^ 2) ≤
      (2 / (L : ℝ)) * A ^ 2 * (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  let S := mrtFactoredUpTo P U
  let g : ℕ → ℝ := fun n => ((S.filter (fun d => d ∣ n)).card : ℝ) ^ 2
  let E := ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹
  have hE : 0 ≤ E := by
    apply prod_nonneg
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    exact inv_nonneg.mpr (by linarith)
  have hpref (n : ℕ) (_hn : n ≤ U) : (∑ i ∈ Icc 1 n, g i) ≤ E ^ 3 * n := by
    have hc := mrt_divisor_count_second_moment S
      (fun _ hd => mrtFactoredUpTo_pos P U hd)
      (fun _ hd _ he hed => mrtFactoredUpTo_divisor_closed P U hd he hed) n
    calc
      _ ≤ (n : ℝ) * (∑ d ∈ S, 1 / (d : ℝ)) ^ 3 := hc
      _ ≤ (n : ℝ) * E ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity))
          (mrt_factored_reciprocal_sum P hP U) 3
      _ = _ := mul_comm _ _
  have ht := mrt_weighted_square_tail g (fun _ => sq_nonneg _) hL hLU
    (pow_nonneg hE 3) hpref
  calc
    _ ≤ ∑ n ∈ Ioc L U, A ^ 2 * (g n / (n : ℝ) ^ 2) := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_natCast, div_pow]
      apply (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hb n hn) 2) (sq_nonneg _)).trans_eq
      dsimp [g]
      ring
    _ = A ^ 2 * ∑ n ∈ Ioc L U, g n / (n : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ A ^ 2 * (2 * E ^ 3 / L) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg A)
    _ = _ := by ring

theorem mrt_mixed_coefficient_mean_square (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial (Ioc L U)
      (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ))
      (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      16 * Real.exp 1 * ((T + U) / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
        (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  have hs : Ioc L U ⊆ Ioc 0 U := by
    intro n hn
    exact mem_Ioc.mpr ⟨lt_of_lt_of_le hL (mem_Ioc.mp hn).1.le, (mem_Ioc.mp hn).2⟩
  apply (mrt_dirichlet_mean_square_subset (Ioc L U) (N := U) hs
    (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ)) hT).trans
  have hmass := mrt_factored_coefficient_mass P hP
    (mrtMixedPrimeCoefficient P M a b r) hL hLU
    (fun n hn => mrt_mixed_prime_coefficient_bound P M hP a b ha hb r
      (lt_of_lt_of_le hL (mem_Ioc.mp hn).1.le) (mem_Ioc.mp hn).2)
  calc
    _ ≤ (8 * Real.exp 1 * (T + U)) *
        ((2 / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
          (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedPolynomial
namespace OAI

/-! Exact prime-power times cofactor polynomial identity. This attaches
the proved mixed coefficient estimate to the actual expression used on
the multiscale large-prime frequency classes. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_multiplicative_phase {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    Complex.exp (((-Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-Real.log ((m * n : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add, Nat.cast_mul, Real.log_mul
    (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]
  congr 1
  push_cast
  ring

lemma mrt_mixed_tuple_term {r : ℕ} (v : Fin r → ℕ)
    (hv : ∀ i, 0 < v i) {m : ℕ} (hm : 0 < m) (a b : ℕ → ℂ) (t : ℝ) :
    (∏ i, (a (v i) / (v i : ℂ)) *
      Complex.exp (((-Real.log (v i : ℝ) * t : ℝ) : ℂ) * Complex.I)) *
      ((b m / (m : ℂ)) *
        Complex.exp (((-Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
      ((∏ i, a (v i)) * b m) / ((∏ i, v i) * m : ℕ) *
        Complex.exp (((-Real.log (((∏ i, v i) * m : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [prod_mul_distrib, prod_div_distrib, mrt_prime_tuple_phase v hv t]
  have hprod : 0 < ∏ i, v i := prod_pos (fun i _ => hv i)
  have he := mrt_multiplicative_phase hprod hm t
  rw [← he]
  push_cast
  ring

theorem mrt_mixed_polynomial_identity (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hM : ∀ m ∈ M, 0 < m)
    (a b : ℕ → ℂ) (r L U : ℕ)
    (hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      L < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U) (t : ℝ) :
    (mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t) ^ r *
      mrtExponentialPolynomial M (fun m => b m / (m : ℂ))
        (fun m => -Real.log (m : ℝ)) t =
      mrtExponentialPolynomial (Ioc L U)
        (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  let V := Fintype.piFinset (fun _ : Fin r => P)
  let S := V ×ˢ M
  let mult : ((Fin r → ℕ) × ℕ) → ℕ := fun v => (∏ i, v.1 i) * v.2
  let coeff : ((Fin r → ℕ) × ℕ) → ℂ := fun v => (∏ i, a (v.1 i)) * b v.2
  let term : ℕ → ℂ := fun n => (n : ℂ)⁻¹ *
    Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I)
  have hmap : ∀ v ∈ S, mult v ∈ Ioc L U := by
    intro v hv
    exact mem_Ioc.mpr (hsupport v.1 (mem_product.mp hv).1 v.2 (mem_product.mp hv).2)
  have hgroup : (∑ n ∈ Ioc L U, ∑ v ∈ S.filter (fun v => mult v = n),
      coeff v * term (mult v)) = ∑ v ∈ S, coeff v * term (mult v) :=
    sum_fiberwise_of_maps_to hmap _
  have hright : mrtExponentialPolynomial (Ioc L U)
      (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ))
      (fun n => -Real.log (n : ℝ)) t = ∑ v ∈ S, coeff v * term (mult v) := by
    rw [← hgroup]
    unfold mrtExponentialPolynomial mrtMixedPrimeCoefficient mrtMixedPrimeFiber
    apply sum_congr rfl
    intro n _
    simp only [sum_div, sum_mul]
    apply sum_congr rfl
    intro v hv
    have he : mult v = n := (mem_filter.mp hv).2
    change coeff v / (n : ℂ) * _ = coeff v * term (mult v)
    rw [he]
    dsimp [term]
    ring
  rw [hright]
  unfold mrtExponentialPolynomial
  rw [sum_pow', sum_mul]
  simp_rw [mul_sum]
  rw [sum_product]
  apply sum_congr rfl
  intro v hv
  apply sum_congr rfl
  intro m hm
  simpa only [coeff, term, mult, div_eq_mul_inv, mul_assoc] using
    mrt_mixed_tuple_term v
      (fun i => (hP _ (Fintype.mem_piFinset.mp hv i)).pos) (hM m hm) a b t

theorem mrt_mixed_prime_cofactor_mean_square (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hM : ∀ m ∈ M, 0 < m)
    (a b : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      L < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖(mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t) ^ r *
        mrtExponentialPolynomial M (fun m => b m / (m : ℂ))
          (fun m => -Real.log (m : ℝ)) t‖ ^ 2) ≤
      16 * Real.exp 1 * ((T + U) / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
        (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  simp_rw [mrt_mixed_polynomial_identity P M hP hM a b r L U hsupport]
  exact mrt_mixed_coefficient_mean_square P M hP a b ha hb r hL hLU hT

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAmplification
namespace OAI

/-! Amplification on the multiscale classes where a preceding short-prime
polynomial is large. The inserted power is estimated by the actual mixed
prime/cofactor moment, not by an assumed large-value proposition. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem mrt_amplified_energy (Q R : ℝ → ℂ) (hQ : Continuous Q) (hR : Continuous R)
    (r : ℕ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖Q t‖) :
    (∫ t in E, ‖R t‖ ^ 2) ≤
      (∫ t in -T..T, ‖Q t ^ r * R t‖ ^ 2) / V ^ (2 * r) := by
  have hprod : Continuous (fun t => Q t ^ r * R t) := (hQ.pow r).mul hR
  have hi := mrt_continuous_square_integrable hprod hT hE
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  calc
    _ = ∫ t in E, V ^ (2 * r) * ‖R t‖ ^ 2 := by
      rw [integral_const_mul]
      ring
    _ ≤ ∫ t in E, ‖Q t ^ r * R t‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => by positivity) _ hi
      intro t ht
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm r 2]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hV.le (hlarge t ht) _) (sq_nonneg _)
    _ ≤ _ := mrt_restricted_square_le_interval hprod hT hE


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCofactorMoment
namespace OAI

/-! The mixed moment needed by the second and later MRT frequency classes.
This is the actual reciprocal-count cofactor, with arbitrary one-bounded
remaining masks. Its only loss is the explicit prime-tuple factorial. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem mrt_short_prime_cofactor_moment (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y N : ℕ} (hY : 0 < Y) (hN : 0 < N)
    (hbin : P ⊆ Icc Y (2 * Y)) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    (r : ℕ) (hpowlo : u ≤ (Y : ℝ) ^ r) (hpowhi : (Y : ℝ) ^ r ≤ u * Y)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖(mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t) ^ r *
        mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      16 * Real.exp 10 * (T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y) *
        (r.factorial : ℝ) ^ 2 := by
  let M := Ioc ⌊(N : ℝ) / u⌋₊ ⌊(2 * N : ℝ) / u⌋₊
  let B : ℕ → ℂ := fun n => F n / ((finitePrimeDivisorCount Q n + 1 : ℕ) : ℂ)
  let U : ℕ := 2 ^ (r + 1) * Y * N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hM (m : ℕ) (hm : m ∈ M) : 0 < m := by
    have := (mem_Ioc.mp hm).1
    omega
  have hwindow (m : ℕ) (hm : m ∈ M) : (N : ℝ) < u * m ∧ u * m ≤ 2 * N := by
    change m ∈ Ioc ⌊(N : ℝ) / u⌋₊ ⌊(2 * N : ℝ) / u⌋₊ at hm
    rw [← mrt_cofactor_window_set N hu] at hm
    exact (mem_filter.mp hm).2
  have hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      N < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U := by
    intro v hv m hm
    have hlo : Y ^ r ≤ ∏ i, v i := by
      calc
        _ = ∏ _i : Fin r, Y := by simp
        _ ≤ _ := prod_le_prod' (fun i _ =>
          (mem_Icc.mp (hbin (Fintype.mem_piFinset.mp hv i))).1)
    have hhi : (∏ i, v i) ≤ (2 * Y) ^ r := by
      calc
        _ ≤ ∏ _i : Fin r, 2 * Y := prod_le_prod' (fun i _ =>
          (mem_Icc.mp (hbin (Fintype.mem_piFinset.mp hv i))).2)
        _ = _ := by simp
    have hloR : u ≤ ((∏ i, v i : ℕ) : ℝ) := hpowlo.trans (by exact_mod_cast hlo)
    have hhiR : ((∏ i, v i : ℕ) : ℝ) ≤ (2 : ℝ) ^ r * u * Y := by
      calc
        _ ≤ ((2 : ℝ) * Y) ^ r := by exact_mod_cast hhi
        _ = (2 : ℝ) ^ r * (Y : ℝ) ^ r := mul_pow _ _ _
        _ ≤ (2 : ℝ) ^ r * (u * Y) :=
          mul_le_mul_of_nonneg_left hpowhi (by positivity)
        _ = _ := by ring
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hw := hwindow m hm
    constructor
    · have hh := hw.1.trans_le (mul_le_mul_of_nonneg_right hloR hm0)
      exact_mod_cast hh
    · have hh : ((∏ i, v i : ℕ) : ℝ) * m ≤
          (2 : ℝ) ^ (r + 1) * Y * N := by
        calc
          _ ≤ ((2 : ℝ) ^ r * u * Y) * m := mul_le_mul_of_nonneg_right hhiR hm0
          _ = ((2 : ℝ) ^ r * Y) * (u * m) := by ring
          _ ≤ ((2 : ℝ) ^ r * Y) * (2 * N) :=
            mul_le_mul_of_nonneg_left hw.2 (by positivity)
          _ = _ := by rw [pow_succ]; ring
      exact_mod_cast hh
  have hNU : N ≤ U := by
    have hp : 1 ≤ 2 ^ (r + 1) := one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))
    have hfactor : 1 ≤ 2 ^ (r + 1) * Y := one_le_mul_of_one_le_of_one_le hp hY
    simpa only [U, one_mul] using Nat.mul_le_mul_right N hfactor
  have hbound := mrt_mixed_prime_cofactor_mean_square P M hP hM a B ha
    (fun m hm => mrt_reciprocal_count_oneBounded Q F hF m (hM m hm))
    r hN hNU hsupport hT
  have he (t : ℝ) : mrtCofactorPolynomial Q F N u t =
      mrtExponentialPolynomial M (fun m => B m / (m : ℂ))
        (fun m => -Real.log (m : ℝ)) t := mrt_cofactor_exponential_polynomial Q F N hu t
  simp_rw [he]
  apply hbound.trans
  have hratio : (T + (U : ℝ)) / (N : ℝ) =
      T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y := by
    dsimp [U]
    push_cast
    field_simp [hNR.ne']
  rw [hratio]
  calc
    _ ≤ 16 * Real.exp 1 * (T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y) *
        (r.factorial : ℝ) ^ 2 * Real.exp 9 :=
      mul_le_mul_of_nonneg_left (mrt_short_bin_euler_cube P hP hY hbin) (by positivity)
    _ = _ := by
      rw [show Real.exp 10 = Real.exp 1 * Real.exp 9 by rw [← Real.exp_add]; norm_num]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiscaleEnergy
namespace OAI

/-! The actual typical-set polynomial on a later MRT frequency class.
The preceding short prime polynomial is large, while each current-bin
polynomial is small. Amplification is applied before extending the
cofactor energy to the whole frequency interval. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem mrt_short_class_cofactor_energy (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y N : ℕ} (hY : 0 < Y) (hN : 0 < N)
    (hbin : P ⊆ Icc Y (2 * Y)) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    (r : ℕ) (hpowlo : u ≤ (Y : ℝ) ^ r) (hpowhi : (Y : ℝ) ^ r ≤ u * Y)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial P
      (fun p => a p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      (16 * Real.exp 10 * (T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y) *
        (r.factorial : ℝ) ^ 2) / V ^ (2 * r) := by
  have hR : Continuous (mrtCofactorPolynomial Q F N u) := by
    have he : mrtCofactorPolynomial Q F N u =
        mrtExponentialPolynomial (Ioc ⌊(N : ℝ) / u⌋₊ ⌊(2 * N : ℝ) / u⌋₊)
          (fun n => (F n / ((finitePrimeDivisorCount Q n + 1 : ℕ) : ℂ)) / (n : ℂ))
          (fun n => -Real.log (n : ℝ)) :=
      funext (mrt_cofactor_exponential_polynomial Q F N hu)
    rw [he]
    exact mrtExponentialPolynomial_continuous _ _ _
  apply (mrt_amplified_energy _ _ (mrtExponentialPolynomial_continuous _ _ _) hR
    r hT.le hV hE hlarge).trans
  exact div_le_div_of_nonneg_right
    (mrt_short_prime_cofactor_moment P Q hP hY hN hbin a ha F hF hu r hpowlo hpowhi hT)
    (pow_nonneg hV.le _)


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

theorem mrt_short_class_cofactor_energy_chosen_oai (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y N : ℕ} (hY : 1 < Y) (hN : 0 < N)
    (hbin : P ⊆ Icc Y (2 * Y)) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial P
      (fun p => a p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      (16 * Real.exp 10 *
        (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder Y u + 1) * Y) *
          ((mrtAmplificationOrder Y u).factorial : ℝ) ^ 2) /
        V ^ (2 * mrtAmplificationOrder Y u) := by
  obtain ⟨hlo, hhi, _⟩ := mrt_amplification_order_bounds
    (show (1 : ℝ) < Y by exact_mod_cast hY) hu
  exact mrt_short_class_cofactor_energy P Q hP (by omega) hN hbin a ha F hF hu _
    hlo hhi hT hV hE hlarge

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_short_class_cofactor_energy_chosen_oai := @OAI.TwoPointCorrelations.mrt_short_class_cofactor_energy_chosen_oai
