-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_liouville_principal_small_height
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:33:32.908331+00:00
-- url     : https://prove2.me/submissions/d67ea82a-5a3e-46d3-8d9c-b770a30f555d

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_modFiveThetaInput

section
-- module Solutions.OAIChowla.OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds
namespace OAI
noncomputable section

open scoped _root_.BigOperators

namespace Problem337


instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩







end Problem337

end

end OAI

end

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePartialSummation
namespace OAI

/-! Exact partial summation, with the prime-count error retained inside the
integral. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem centered_partial_summation (c : ℕ → ℝ) (α a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ t in a..b, f t) =
      f b * (partialCoefficientSum c b - α * b) -
      f a * (partialCoefficientSum c a - α * a) -
      ∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t) := by
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab
  have hdfi : IntervalIntegrable (deriv f) volume a b :=
    hdf.intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun t => deriv f t * t) volume a b :=
    hdfi.mul_continuousOn continuous_id.continuousOn
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum c t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc c ha
      (hdf.integrableOn_Icc)
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha hab hf hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  change (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
    f b * partialCoefficientSum c b - f a * partialCoefficientSum c a -
      ∫ t in a..b, deriv f t * partialCoefficientSum c t at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x (_ : x ∈ Set.uIcc a b) => hasDerivAt_id x) hdfi intervalIntegrable_const
  simp only [id_eq] at hparts
  have hsplit : (∫ t in a..b, deriv f t * t + f t * 1) =
      (∫ t in a..b, deriv f t * t) + ∫ t in a..b, f t := by
    simp only [mul_one]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum c t) -
        α * (∫ t in a..b, deriv f t * t) := by
    simp only [mul_sub, show ∀ t, deriv f t * (α * t) = α * (deriv f t * t) by
      intro t; ring]
    rw [intervalIntegral.integral_sub hsum (hdmain.const_mul α),
      intervalIntegral.integral_const_mul]
  rw [herr, hAbel]
  linear_combination -α * hparts


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ThetaLogError
namespace OAI

/-! An integrable logarithmic error bound obtained from the stated exponential
prime-number error. It also pays exactly for finite exceptional prime sets. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma exp_neg_sqrt_log_le (c x : ℝ) (hc : 0 < c) (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / (c ^ 4 * Real.log x ^ 2) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hsq := Real.sq_sqrt hl.le
  have hpow : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    calc
      _ = c ^ 4 * ((Real.sqrt (Real.log x)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have he := Real.pow_div_factorial_le_exp (c * Real.sqrt (Real.log x))
    (mul_nonneg hc.le (Real.sqrt_nonneg (Real.log x))) 4
  norm_num at he
  rw [hpow] at he
  have hmul := mul_le_mul_of_nonneg_right he
    (Real.exp_pos (-c * Real.sqrt (Real.log x))).le
  have hexp : Real.exp (c * Real.sqrt (Real.log x)) *
      Real.exp (-c * Real.sqrt (Real.log x)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hexp] at hmul
  apply (le_div_iff₀ (by positivity : 0 < c ^ 4 * Real.log x ^ 2)).mpr
  nlinarith [hmul]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPrimeBands
namespace OAI

/-! Quantitative reciprocal-prime bands from the actual theta error.
Partial summation gives the reciprocal-prime estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma reciprocalLog_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt reciprocalLog
      (-(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hh := (hasDerivAt_inv hx0).div (Real.hasDerivAt_log hx0) hl0
  convert (preTransparency := .instances) hh using 1
  · rfl
  · field_simp
    ring




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedThetaError
namespace OAI

/-! The bounded-error form of partial summation needed for the padding
oscillation. The constants retain the uniform derivative bounds explicitly. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem weighted_theta_error (c : ℕ → ℝ) (α K F D a b : ℝ)
    (hK : 0 ≤ K) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b))
    (hsize : ∀ x ∈ Set.Icc a b, |f x| ≤ F / x)
    (hdsize : ∀ x ∈ Set.Icc a b, |deriv f x| ≤ D / x ^ 2)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ x in a..b, f x)| ≤
      (2 * F + D) * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hb1 : 1 < b := ha1.trans_le hab
  have hla : 1 ≤ Real.log a := by simpa using Real.log_le_log (Real.exp_pos 1) ha
  have hlap : 0 < Real.log a := Real.log_pos ha1
  have hxp (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 < x := ha0.trans_le hx.1
  have hlx (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x :=
    hla.trans (Real.log_le_log ha0 hx.1)
  have hln (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log x ≠ 0 :=
    (zero_lt_one.trans_le (hlx x hx)).ne'
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |f x * (partialCoefficientSum c x - α * x)| ≤ F * K / Real.log a := by
    have hx0 := hxp x hx
    have hl0 := hln x hx
    rw [abs_mul]
    calc
      _ ≤ (F / x) * (K * x / Real.log x ^ 2) :=
        mul_le_mul (hsize x hx) (hE x hx) (abs_nonneg _) (by positivity)
      _ = F * K / Real.log x ^ 2 := by field_simp
      _ ≤ F * K / Real.log a := by
        apply div_le_div_of_nonneg_left (mul_nonneg hF hK) hlap
        have hm := Real.log_le_log ha0 hx.1
        nlinarith [sq_nonneg (Real.log x - 1), hlx x hx]
  have hderror (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |deriv f x * (partialCoefficientSum c x - α * x)| ≤
        (D * K) * (x⁻¹ / Real.log x ^ 2) := by
    have hx0 := hxp x hx
    have hl0 := hln x hx
    rw [abs_mul]
    calc
      _ ≤ (D / x ^ 2) * (K * x / Real.log x ^ 2) :=
        mul_le_mul (hdsize x hx) (hE x hx) (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxp x hx).ne').continuousWithinAt
  have hg : IntervalIntegrable (fun x : ℝ => (D * K) * (x⁻¹ / Real.log x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    exact ((continuousOn_id.inv₀ (fun x hx => (hxp x hx).ne')).div
      (hclog.pow 2) (fun x hx => pow_ne_zero 2 (hln x hx))).const_mul (D * K)
  have hi : |∫ x in a..b, deriv f x * (partialCoefficientSum c x - α * x)| ≤
      D * K / Real.log a := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hderror x ⟨hx.1.le, hx.2⟩)) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_div_log_sq ha1 hb1] at hh
    apply hh.trans
    have hbnonneg : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr (Real.log_pos hb1).le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg (mul_nonneg hD hK) hbnonneg]
  rw [centered_partial_summation c α a b ha0.le hab f hf hdf]
  calc
    _ ≤ |f b * (partialCoefficientSum c b - α * b)| +
        |f a * (partialCoefficientSum c a - α * a)| +
        |∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ F * K / Real.log a + F * K / Real.log a + D * K / Real.log a :=
      add_le_add (add_le_add (hbound b ⟨hab, le_rfl⟩) (hbound a ⟨le_rfl, hab⟩)) hi
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.OscillatoryThetaError
namespace OAI

/-! Uniform partial summation for `(1-cos(t log p))/p`, with `|t|≤2`.
The oscillatory prime estimate is deduced from the theta error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma reciprocalLog_size {x : ℝ} (hx : 1 < x) (hl : 1 ≤ Real.log x) :
    |reciprocalLog x| ≤ 1 / x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl0 : 0 < Real.log x := zero_lt_one.trans_le hl
  unfold reciprocalLog
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hl0).mpr
  have hh := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hx0.le)
  simpa only [mul_one, one_div] using hh

lemma reciprocalLog_deriv_size {x : ℝ} (hx : 1 < x) (hl : 1 ≤ Real.log x) :
    |deriv reciprocalLog x| ≤ 2 / x ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl0 : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [(reciprocalLog_hasDerivAt hx).deriv, abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < Real.log x + 1),
    abs_of_pos (by positivity : 0 < x ^ 2 * Real.log x ^ 2)]
  calc
    _ ≤ (2 * Real.log x ^ 2) / (x ^ 2 * Real.log x ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (Real.log x - 1)]
    _ = _ := by field_simp

lemma oscillatoryReciprocalLog_hasDerivAt (t x : ℝ) (hx : 1 < x) :
    HasDerivAt (oscillatoryReciprocalLog t)
      ((t * Real.sin (t * Real.log x) / x) * reciprocalLog x +
        (1 - Real.cos (t * Real.log x)) * deriv reciprocalLog x) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hg := ((Real.hasDerivAt_cos (t * Real.log x)).comp x
    ((Real.hasDerivAt_log hx0).const_mul t)).const_sub 1
  have hh := hg.mul (reciprocalLog_hasDerivAt hx)
  convert (preTransparency := .instances) hh using 1
  · rfl
  · rw [(reciprocalLog_hasDerivAt hx).deriv]
    simp only [div_eq_mul_inv, Function.comp_def]
    ring



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CosineLogIntegral
namespace OAI

/-! The elementary logarithmic oscillatory integral behind the padding
prime estimate. All constants are absolute. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory
open scoped _root_.Classical

lemma integral_inverse_square (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b, (y ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hderiv : ∀ y ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -y⁻¹) ((y ^ 2)⁻¹) y := by
    intro y hy
    have hy' : y ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hy
    have hy0 : y ≠ 0 := (ha.trans_le hy'.1).ne'
    convert! (preTransparency := .instances) (hasDerivAt_inv hy0).neg using 1
    simp
  have hc : ContinuousOn (fun y : ℝ => (y ^ 2)⁻¹) (Set.Icc a b) := by
    intro y hy
    have hy0 : y ≠ 0 := (ha.trans_le hy.1).ne'
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hy0)).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hc.intervalIntegrable_of_Icc hab)
  linarith

lemma cosine_log_tail (T a b : ℝ) (hT : 0 < T) (ha : 0 < a) (hab : a ≤ b)
    (hTa : 1 ≤ T * a) :
    |∫ y in a..b, Real.cos (T * y) / y| ≤ 3 := by
  have hb : 0 < b := ha.trans_le hab
  have hpos (y : ℝ) (hy : y ∈ Set.Icc a b) : 0 < y := ha.trans_le hy.1
  have hu (y : ℝ) : HasDerivAt (fun y => Real.sin (T * y) / T) (Real.cos (T * y)) y := by
    have hh := ((Real.hasDerivAt_sin (T * y)).comp y ((hasDerivAt_id y).const_mul T)).div_const T
    convert (preTransparency := .instances) hh using 1
    · simp only [Function.comp_def, mul_comm T]
    · field_simp
  have hv (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(y ^ 2)⁻¹) y := by
    apply hasDerivAt_inv
    have hy' : y ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hy
    exact (ha.trans_le hy'.1).ne'
  have hcos : IntervalIntegrable (fun y => Real.cos (T * y) / y) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    exact (by fun_prop (disch := exact (hpos y hy).ne') :
      ContinuousAt (fun y => Real.cos (T * y) / y) y).continuousWithinAt
  have htail : IntervalIntegrable (fun y => Real.sin (T * y) / (T * y ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    have hy0 := (hpos y hy).ne'
    exact (by fun_prop (disch := positivity) :
      ContinuousAt (fun y => Real.sin (T * y) / (T * y ^ 2)) y).continuousWithinAt
  have hvin : IntervalIntegrable (fun y : ℝ => -(y ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    exact (((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (hpos y hy).ne')).neg).continuousWithinAt
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun y (_ : y ∈ Set.uIcc a b) => hu y) hv
    ((by fun_prop : Continuous (fun y => Real.cos (T * y))).intervalIntegrable a b) hvin
  have heq : (∫ y in a..b, Real.cos (T * y) / y) -
      (∫ y in a..b, Real.sin (T * y) / (T * y ^ 2)) =
      Real.sin (T * b) / (T * b) - Real.sin (T * a) / (T * a) := by
    rw [← intervalIntegral.integral_sub hcos htail]
    convert (preTransparency := .instances) hparts using 1
    · apply intervalIntegral.integral_congr
      intro y _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · field_simp
  have hendpoint (y : ℝ) (hy : a ≤ y) : |Real.sin (T * y) / (T * y)| ≤ 1 := by
    have hy0 : 0 < y := ha.trans_le hy
    rw [abs_div, abs_of_pos (mul_pos hT hy0)]
    apply (div_le_one (mul_pos hT hy0)).mpr
    exact (Real.abs_sin_le_one _).trans (hTa.trans (mul_le_mul_of_nonneg_left hy hT.le))
  have hg : IntervalIntegrable (fun y : ℝ => T⁻¹ * (y ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    exact (((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (hpos y hy).ne')).const_mul _).continuousWithinAt
  have hi : |∫ y in a..b, Real.sin (T * y) / (T * y ^ 2)| ≤ 1 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun y : ℝ => Real.sin (T * y) / (T * y ^ 2))
      (g := fun y : ℝ => T⁻¹ * (y ^ 2)⁻¹) hab
      (Filter.Eventually.of_forall (fun y hy => by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hT (sq_pos_of_pos (hpos y ⟨hy.1.le, hy.2⟩)))]
        calc
          _ ≤ 1 / (T * y ^ 2) := div_le_div_of_nonneg_right (Real.abs_sin_le_one _)
            (mul_nonneg hT.le (sq_nonneg y))
          _ = _ := by simp [div_eq_mul_inv, mul_inv_rev, mul_comm])) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_inverse_square a b ha hab] at hh
    have hsmall : T⁻¹ * a⁻¹ ≤ 1 := by
      rw [← mul_inv_rev]
      exact (inv_le_one₀ (mul_pos ha hT)).mpr (by nlinarith)
    have hnonneg : 0 ≤ T⁻¹ * b⁻¹ := by positivity
    nlinarith
  have htriangle := abs_sub (Real.sin (T * b) / (T * b)) (Real.sin (T * a) / (T * a))
  have htriangle' := abs_add_le
    (Real.sin (T * b) / (T * b) - Real.sin (T * a) / (T * a))
    (∫ y in a..b, Real.sin (T * y) / (T * y ^ 2))
  have hformula : (∫ y in a..b, Real.cos (T * y) / y) =
      (Real.sin (T * b) / (T * b) - Real.sin (T * a) / (T * a)) +
      (∫ y in a..b, Real.sin (T * y) / (T * y ^ 2)) := by linarith
  rw [hformula]
  linarith [hendpoint a le_rfl, hendpoint b hab]




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CharacterTwists
namespace OAI

/-!
# Dirichlet character twists preserve uniform nonpretentiousness

Characters with different moduli are multiplied after changing both levels
to the product modulus. The resulting character equals the pointwise product
on every natural number, including the nonunit classes. This gives an exact
identity of pretentious distances and preserves the original height cutoff.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter



@[simp] lemma conjugateCharacter_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    conjugateCharacter χ n = conj (χ n) := rfl








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.Dilation
namespace OAI

/-!
# Finite multiplicative expansion of a dilation

This is the arithmetic content of manuscript Lemma `lem:affine-dilation`.
The equality is asserted for positive arguments, the domain relevant to
ordinary multiplicative functions. No complete multiplicativity is used.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations










@[simp] theorem dilationComponent_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationComponent a f E 1 = 1 := by
  simp [dilationComponent, localComponent]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
namespace OAI

/-!
# Residue classes as finite multiplicative expansions

The character identity in manuscript Lemma `lem:affine-residue` includes
nonunit residue classes. Dividing by the gcd reduces to a unit class, so the
standard character orthogonality relation applies even when the reduced
modulus is one. Each resulting dilation has the finite expansion already
proved in `Dilation`.
-/

open scoped _root_.BigOperators _root_.ComplexConjugate

namespace TwoPointCorrelations




@[simp] lemma naturalCharacter_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    naturalCharacter χ 1 = 1 := by simp [naturalCharacter]














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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrincipalPsi
namespace OAI

/-! The principal character only removes powers of five.  For the required
error bound it is enough to charge the prime 5 once, and all remaining
terms to the already proved elementary prime-power error. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem
namespace OAI

/-! The fixed modulus-five prime number theorem follows from the three
nonprincipal contour estimates, the zeta prime number theorem, and finite
character orthogonality. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩







end TwoPointCorrelations

end OAI

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

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


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







theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

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

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

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

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩





lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top


private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp





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











theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply Real.log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind



theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply Real.log_pos; norm_num
        linarith [E₁.nonneg]




























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

/-- Mertens' second theorem implies the reciprocal-prime estimate. -/
theorem primeReciprocalInput : PrimeReciprocalInput := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun x hx => ?_⟩
  rw [sievePrimesUpTo_eq_Ioc]
  exact hC x hx

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeBands
namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The reciprocal-mass bounds follow from Mertens’ theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mrt_sievePrimesUpTo_mono {P Q : ℝ} (hPQ : P ≤ Q) :
    sievePrimesUpTo P ⊆ sievePrimesUpTo Q := by
  intro p hp
  rcases mem_filter.mp hp with ⟨hp, hprime⟩
  exact mem_filter.mpr ⟨mem_Iic.mpr ((mem_Iic.mp hp).trans (Nat.floor_mono hPQ)), hprime⟩

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

lemma mrtPrimeBand_mass {P Q : ℝ} (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) =
      (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
        ∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ) := by
  exact sum_sdiff_eq_sub (f := fun p : ℕ => (1 : ℝ) / p) (mrt_sievePrimesUpTo_mono hPQ)

/-- Uniform bounded-error reciprocal mass for every positive prime band. -/
theorem mrt_prime_band_mertens : ∃ C : ℝ, 0 ≤ C ∧
    ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      |(∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) -
        (Real.log (Real.log Q) - Real.log (Real.log P))| ≤ C := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨2 * C, by positivity, ?_⟩
  intro P Q hP hPQ
  rw [mrtPrimeBand_mass hPQ]
  have hQ := hP.trans hPQ
  have he : (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
      (∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) -
      (Real.log (Real.log Q) - Real.log (Real.log P)) =
      ((∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) - Real.log (Real.log Q)) -
      ((∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) - Real.log (Real.log P)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hC Q hQ, hC P hP])


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeOscillation
namespace OAI

/-! The moderate-frequency prime-phase step in MRT Lemma A.4.
The frequency dependence of partial summation is explicit, so a growing
frequency range can be paid for by the exponential prime-number error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_oscillatory_weight_bounds (t x : ℝ) (hx : 1 < x)
    (hl : 1 ≤ Real.log x) :
    |oscillatoryReciprocalLog t x| ≤ 2 / x ∧
      |deriv (oscillatoryReciprocalLog t) x| ≤ (|t| + 4) / x ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hg : |1 - Real.cos (t * Real.log x)| ≤ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith [Real.neg_one_le_cos (t * Real.log x)]
  have hs : |t * Real.sin (t * Real.log x) / x| ≤ |t| / x := by
    rw [abs_div, abs_mul, abs_of_pos hx0]
    apply div_le_div_of_nonneg_right _ hx0.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.abs_sin_le_one (t * Real.log x)) (abs_nonneg t)
  have hrec := reciprocalLog_size hx hl
  have hdrec := reciprocalLog_deriv_size hx hl
  constructor
  · unfold oscillatoryReciprocalLog
    rw [abs_mul]
    calc
      _ ≤ 2 * (1 / x) := mul_le_mul hg hrec (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  · rw [(oscillatoryReciprocalLog_hasDerivAt t x hx).deriv]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (|t| / x) * (1 / x) + 2 * (2 / x ^ 2) :=
        add_le_add (mul_le_mul hs hrec (abs_nonneg _) (by positivity))
          (mul_le_mul hg hdrec (abs_nonneg _) (by norm_num))
      _ = _ := by ring

theorem halasz_oscillatory_theta_error (c : ℕ → ℝ) (α K a b t : ℝ)
    (hK : 0 ≤ K) (ha : Real.exp 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t n * c n) -
      α * (∫ x in a..b, oscillatoryReciprocalLog t x)| ≤
        (8 + |t|) * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hx1 (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 < x := ha1.trans_le hx.1
  have hl (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (ha.trans hx.1)
  have hh := weighted_theta_error c α K 2 (|t| + 4) a b hK (by norm_num)
    (by positivity) ha hab (oscillatoryReciprocalLog t)
    (fun x hx => (oscillatoryReciprocalLog_hasDerivAt t x (hx1 x hx)).differentiableAt)
    (fun x hx => ?_)
    (fun x hx => (halasz_oscillatory_weight_bounds t x (hx1 x hx) (hl x hx)).1)
    (fun x hx => (halasz_oscillatory_weight_bounds t x (hx1 x hx) (hl x hx)).2) hE
  · convert (preTransparency := .instances) hh using 1
    ring
  · have hxn : x ≠ 0 := (zero_lt_one.trans (hx1 x hx)).ne'
    have hln : Real.log x ≠ 0 := (Real.log_pos (hx1 x hx)).ne'
    have hc : ContDiffAt ℝ 2 (oscillatoryReciprocalLog t) x := by
      unfold oscillatoryReciprocalLog reciprocalLog
      fun_prop (disch := assumption)
    exact (hc.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt



end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeTheta
namespace OAI

/-! A uniform tail form of the fixed-modulus prime-number
estimate. Its exponentially decreasing constant pays for the growing
frequency factor in the moderate-frequency partial summation. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_prime_log_weight_split (n : ℕ) :
    halaszPrimeLogWeight n = modFiveLogWeight true n + modFiveLogWeight false n := by
  by_cases hn : n.Prime <;> by_cases hr : n % 5 = 1 <;>
    simp [halaszPrimeLogWeight, modFiveLogWeight, ModFivePrime, hn, hr]

lemma halasz_prime_theta_split (x : ℝ) :
    partialCoefficientSum halaszPrimeLogWeight x = modFiveTheta true x + modFiveTheta false x := by
  unfold partialCoefficientSum modFiveTheta
  simp_rw [halasz_prime_log_weight_split, sum_add_distrib]

theorem ModFiveThetaInput.halasz_prime_tail_error (hP : ModFiveThetaInput) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ a x : ℝ, 2 ≤ a → a ≤ x →
      |partialCoefficientSum halaszPrimeLogWeight x - x| ≤
        (K * Real.exp (-c * Real.sqrt (Real.log a))) * x / Real.log x ^ 2 := by
  obtain ⟨c, C, hc, hC, htheta⟩ := hP
  refine ⟨c / 2, 48 * C / (c / 2) ^ 4, by positivity, by positivity, ?_⟩
  intro a x ha hax
  have hx : 2 ≤ x := ha.trans hax
  have hxp : 0 < x := by linarith
  have hap : 0 < a := by linarith
  have hx1 : 1 < x := by linarith
  have hsum : |partialCoefficientSum halaszPrimeLogWeight x - x| ≤
      2 * C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    rw [halasz_prime_theta_split]
    have he : modFiveTheta true x + modFiveTheta false x - x =
        (modFiveTheta true x - modFiveDensity true * x) +
          (modFiveTheta false x - modFiveDensity false * x) := by
      norm_num [modFiveDensity]
      ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add (htheta true x hx)
      (htheta false x hx)).trans_eq (by ring))
  have hhalf : 0 < c / 2 := by positivity
  have hpoly := exp_neg_sqrt_log_le (c / 2) x hhalf hx1
  have hmono : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log a)) := by
    apply Real.exp_le_exp.mpr
    have hs := Real.sqrt_le_sqrt (Real.log_le_log hap hax)
    nlinarith
  have hexp : Real.exp (-c * Real.sqrt (Real.log x)) =
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) *
        Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply hsum.trans
  rw [hexp]
  have hb := mul_le_mul hpoly hmono (Real.exp_pos _).le (by positivity)
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * C * x by positivity)
  convert (preTransparency := .instances) hh using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePhase
namespace OAI

/-! Prime phase sums on a finite real interval. The prime-number error
retains its exponentially small lower-endpoint factor and its explicit
frequency dependence. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_prime_band_filter (a b : ℝ) :
    mrtPrimeBand a b = (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
  ext p
  simp only [mrtPrimeBand, sievePrimesUpTo, mem_sdiff, mem_filter, mem_Iic, mem_Ioc]
  by_cases hp : p.Prime <;> simp only [hp, and_true, and_false, not_false_eq_true]
  omega

lemma halasz_prime_phase_sum (a b t : ℝ) :
    (∑ p ∈ mrtPrimeBand a b, (1 - Real.cos (t * Real.log p)) / p) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t n * halaszPrimeLogWeight n := by
  rw [halasz_prime_band_filter, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · rw [if_pos hp, halaszPrimeLogWeight, if_pos hp]
    have hl : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    unfold oscillatoryReciprocalLog reciprocalLog
    field_simp
  · simp [halaszPrimeLogWeight, hp]

theorem ModFiveThetaInput.halasz_prime_phase_error (hP : ModFiveThetaInput) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ a b t : ℝ, Real.exp 1 ≤ a → a ≤ b →
      |(∑ p ∈ mrtPrimeBand a b, (1 - Real.cos (t * Real.log p)) / p) -
        (∫ x in a..b, oscillatoryReciprocalLog t x)| ≤
          (8 + |t|) * K * Real.exp (-c * Real.sqrt (Real.log a)) / Real.log a := by
  obtain ⟨c, K, hc, hK, htail⟩ := hP.halasz_prime_tail_error
  refine ⟨c, K, hc, hK, ?_⟩
  intro a b t ha hab
  have ha2 : 2 ≤ a := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hh := halasz_oscillatory_theta_error halaszPrimeLogWeight 1
    (K * Real.exp (-c * Real.sqrt (Real.log a))) a b t (by positivity) ha hab
    (fun x hx => by simpa only [one_mul] using htail a x ha2 hx.1)
  rw [← halasz_prime_phase_sum, one_mul] at hh
  convert (preTransparency := .instances) hh using 1
  ring

lemma halasz_log_phase_substitution (a b t : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, oscillatoryReciprocalLog t x) =
      ∫ y in Real.log a..Real.log b, (1 - Real.cos (t * y)) / y := by
  have hxp (x : ℝ) (hx : x ∈ Set.uIcc a b) : 0 < x := by
    rw [Set.uIcc_of_le hab] at hx
    exact (zero_lt_one.trans ha).trans_le hx.1
  have hd (x : ℝ) (hx : x ∈ Set.uIcc a b) := Real.hasDerivAt_log (hxp x hx).ne'
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc a b) :=
    continuousOn_id.inv₀ (fun x hx => (hxp x hx).ne')
  have hg : ContinuousOn (fun y : ℝ => (1 - Real.cos (t * y)) / y)
      (Real.log '' Set.uIcc a b) := by
    rintro y ⟨x, hx, rfl⟩
    have hx' : a ≤ x := by rw [Set.uIcc_of_le hab] at hx; exact hx.1
    have hn : Real.log x ≠ 0 := (Real.log_pos (ha.trans_le hx')).ne'
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun y : ℝ => (1 - Real.cos (t * y)) / y) (Real.log x)).continuousWithinAt
  rw [← intervalIntegral.integral_comp_mul_deriv' hd hc hg]
  apply intervalIntegral.integral_congr
  intro x _
  unfold oscillatoryReciprocalLog reciprocalLog
  simp only [Function.comp_def, div_eq_mul_inv]
  ring





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCosineLower
namespace OAI

/-! A lower bound for the logarithmic cosine integral uniform even at
frequency zero, and the resulting one-sided prime cosine estimate. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset
open scoped _root_.Classical

lemma mrt_cosine_log_integrable (t a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => Real.cos (t * y) / y) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro y hy
  have hn := (ha.trans_le hy.1).ne'
  exact (by fun_prop (disch := assumption) :
    ContinuousAt (fun y : ℝ => Real.cos (t * y) / y) y).continuousWithinAt

lemma mrt_cosine_log_nonneg (t a b : ℝ) (ht : 0 ≤ t) (ha : 0 < a)
    (hab : a ≤ b) (hb : t * b ≤ 1) :
    0 ≤ ∫ y in a..b, Real.cos (t * y) / y := by
  apply intervalIntegral.integral_nonneg hab
  intro y hy
  have hy0 : 0 < y := ha.trans_le hy.1
  have hty : 0 ≤ t * y := mul_nonneg ht hy0.le
  have hty1 : t * y ≤ 1 := (mul_le_mul_of_nonneg_left hy.2 ht).trans hb
  apply div_nonneg _ hy0.le
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> linarith [Real.pi_gt_three]

lemma mrt_cosine_log_lower_pos (t a b : ℝ) (ht : 0 < t) (ha : 0 < a)
    (hab : a ≤ b) : -3 ≤ ∫ y in a..b, Real.cos (t * y) / y := by
  by_cases hta : 1 ≤ t * a
  · exact (abs_le.mp (cosine_log_tail t a b ht ha hab hta)).1
  by_cases htb : t * b ≤ 1
  · exact (by norm_num : (-3 : ℝ) ≤ 0).trans (mrt_cosine_log_nonneg t a b ht.le ha hab htb)
  let c := 1 / t
  have hc : 0 < c := by dsimp [c]; positivity
  have hac : a ≤ c := by
    dsimp [c]
    apply (le_div_iff₀ ht).mpr
    nlinarith only [le_of_not_ge hta]
  have hcb : c ≤ b := by
    dsimp [c]
    apply (div_le_iff₀ ht).mpr
    nlinarith only [le_of_not_ge htb]
  have htc : t * c = 1 := by dsimp [c]; field_simp
  have hhead := mrt_cosine_log_nonneg t a c ht.le ha hac htc.le
  have htail := (abs_le.mp (cosine_log_tail t c b ht hc hcb htc.ge)).1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (mrt_cosine_log_integrable t a c ha hac) (mrt_cosine_log_integrable t c b hc hcb)]
  linarith

lemma mrt_cosine_log_lower (t a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    -3 ≤ ∫ y in a..b, Real.cos (t * y) / y := by
  by_cases ht : t = 0
  · subst t
    exact (by norm_num : (-3 : ℝ) ≤ 0).trans
      (mrt_cosine_log_nonneg 0 a b (by norm_num) ha hab (by norm_num))
  have hcos (y : ℝ) : Real.cos (|t| * y) = Real.cos (t * y) := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, neg_mul, Real.cos_neg]
  simpa only [hcos] using mrt_cosine_log_lower_pos |t| a b (abs_pos.mpr ht) ha hab

lemma mrt_logarithmic_phase_upper (a b t : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, oscillatoryReciprocalLog t x) ≤
      Real.log (Real.log b) - Real.log (Real.log a) + 3 := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log (zero_lt_one.trans ha) hab
  have hlb : 0 < Real.log b := hla.trans_le hlab
  have h₁ : IntervalIntegrable (fun y : ℝ => 1 / y) volume (Real.log a) (Real.log b) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlab
    intro y hy
    exact (continuousAt_const.div continuousAt_id (hla.trans_le hy.1).ne').continuousWithinAt
  have h₂ := mrt_cosine_log_integrable t (Real.log a) (Real.log b) hla hlab
  have he : (∫ y in Real.log a..Real.log b, (1 - Real.cos (t * y)) / y) =
      Real.log (Real.log b / Real.log a) -
        ∫ y in Real.log a..Real.log b, Real.cos (t * y) / y := by
    rw [← integral_one_div_of_pos hla hlb, ← intervalIntegral.integral_sub h₁ h₂]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [halasz_log_phase_substitution a b t ha hab, he, Real.log_div hlb.ne' hla.ne']
  have hh := mrt_cosine_log_lower t (Real.log a) (Real.log b) hla hlab
  linarith

theorem mrt_prime_cosine_lower : ∃ c K C : ℝ, 0 < c ∧ 0 ≤ K ∧ 0 ≤ C ∧
    ∀ a b t : ℝ, Real.exp 1 ≤ a → a ≤ b →
      -C - (8 + |t|) * K * Real.exp (-c * Real.sqrt (Real.log a)) / Real.log a ≤
        ∑ p ∈ mrtPrimeBand a b, Real.cos (t * Real.log p) / p := by
  obtain ⟨c, K, hc, hK, herr⟩ := modFiveThetaInput.halasz_prime_phase_error
  obtain ⟨C, hC, hmass⟩ := mrt_prime_band_mertens
  refine ⟨c, K, C + 3, hc, hK, by positivity, ?_⟩
  intro a b t ha hab
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have ha2 : 2 ≤ a := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hE := (abs_le.mp (herr a b t ha hab)).2
  have hM := (abs_le.mp (hmass a b ha2 hab)).1
  have hI := mrt_logarithmic_phase_upper a b t ha1 hab
  have he : (∑ p ∈ mrtPrimeBand a b, (1 - Real.cos (t * Real.log p)) / p) =
      (∑ p ∈ mrtPrimeBand a b, 1 / (p : ℝ)) -
        ∑ p ∈ mrtPrimeBand a b, Real.cos (t * Real.log p) / p := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    ring
  rw [he] at hE
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLiouvillePrimitive
namespace OAI

/-! On the actual Liouville prime tail, every prime is larger than the
allowed character modulus. Passing to the primitive character therefore
leaves the prime sum exactly unchanged. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma mrt_liouville_tail_above_modulus {X q : ℕ}
    (hX : 1≤ Real.log (X:ℝ))
    (hq : (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ))
    {p : ℕ} (hp : p∈mrtLiouvillePrimeTail X) : q< p := by
  have hlower := (mrtPrimeBand_bounds (Real.exp_pos _).le (Nat.cast_nonneg X) hp).1
  have hpow : (Real.log (X:ℝ))^(1/125:ℝ)≤(Real.log (X:ℝ))^(3/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hexp : (Real.log (X:ℝ))^(3/4:ℝ)<
      Real.exp ((Real.log (X:ℝ))^(3/4:ℝ)) := by
    linarith [Real.add_one_le_exp ((Real.log (X:ℝ))^(3/4:ℝ))]
  have hh : (q:ℝ)< p := lt_of_le_of_lt (hq.trans hpow) (hexp.trans hlower)
  exact_mod_cast hh



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrincipalSmallHeight
namespace OAI

/-! The principal character in the low-height Liouville prime-tail range,
from the proved prime-number theorem and a uniform cosine integral bound. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.Classical _root_.Topology

lemma mrt_small_height_phase_error (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, |t| ≤ Real.exp (L ^ (1 / 3 : ℝ)) →
      (8 + |t|) * K * Real.exp (-c * L ^ (3 / 8 : ℝ)) / L ^ (3 / 4 : ℝ) ≤ 1 := by
  have hg := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 24 by norm_num)).eventually
    (eventually_ge_atTop (2 / c))
  have hd := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (c / 2) (by positivity)).comp
    (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 8 by norm_num))
  simp only [Real.rpow_zero, one_mul] at hd
  have hd' : Tendsto (fun L : ℝ => 9 * K * Real.exp (-(c / 2) * L ^ (3 / 8 : ℝ)))
      atTop (𝓝 0) := by simpa using hd.const_mul (9 * K)
  have he := hd'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hg, he] with L hL hg he
  intro t ht
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hsum : L ^ (1 / 3 : ℝ) * L ^ (1 / 24 : ℝ) = L ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hL0.le (1 / 3))
  rw [hsum] at hm
  have hsmall : L ^ (1 / 3 : ℝ) ≤ (c / 2) * L ^ (3 / 8 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ c / 2 by positivity)
    have heq : (c / 2) * (L ^ (1 / 3 : ℝ) * (2 / c)) = L ^ (1 / 3 : ℝ) := by field_simp
    rw [heq] at hh
    exact hh
  have hexp : Real.exp (L ^ (1 / 3 : ℝ)) * Real.exp (-c * L ^ (3 / 8 : ℝ)) ≤
      Real.exp (-(c / 2) * L ^ (3 / 8 : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hone : 1 ≤ Real.exp (L ^ (1 / 3 : ℝ)) :=
    Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have hmain : (8 + |t|) * K * Real.exp (-c * L ^ (3 / 8 : ℝ)) ≤
      9 * K * Real.exp (-(c / 2) * L ^ (3 / 8 : ℝ)) := by
    calc
      _ ≤ (9 * Real.exp (L ^ (1 / 3 : ℝ))) * K * Real.exp (-c * L ^ (3 / 8 : ℝ)) := by
        gcongr
        linarith
      _ = (9 * K) * (Real.exp (L ^ (1 / 3 : ℝ)) * Real.exp (-c * L ^ (3 / 8 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hden : 1 ≤ L ^ (3 / 4 : ℝ) := Real.one_le_rpow hL (by norm_num)
  exact (div_le_self (by positivity) hden).trans (hmain.trans he.le)

lemma mrt_principal_twist_re {q : ℕ} (hq : 0 < q) {p : ℕ}
    (hp : p.Prime) (hqp : q < p) (t : ℝ) :
    (characterTwist (1 : DirichletCharacter ℂ q) t p).re = Real.cos (t * Real.log (p : ℝ)) := by
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact (not_le_of_gt hqp) (Nat.le_of_dvd hq h))
  have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hcop
  unfold characterTwist
  rw [MulChar.one_apply hu, one_mul, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    sub_zero, Real.exp_zero, one_mul]

theorem mrt_liouville_principal_small_height_oai : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ t : ℝ, |t| ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 / 3 : ℝ)) →
        -C ≤ (∑ p ∈ mrtLiouvillePrimeTail X,
          characterTwist (1 : DirichletCharacter ℂ q) t p / (p : ℂ)).re := by
  obtain ⟨c, K, C, hc, hK, hC, hprime⟩ := mrt_prime_cosine_lower
  refine ⟨C + 1, by positivity, ?_⟩
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (mrt_small_height_phase_error c K hc hK),
    hlog.eventually (eventually_ge_atTop (1 : ℝ))] with X herr hL
  intro q hq hqX t ht
  have hL0 : 0 < Real.log (X : ℝ) := by linarith
  have hX0 : (0 : ℝ) < X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hL0)
  let a := Real.exp ((Real.log (X : ℝ)) ^ (3 / 4 : ℝ))
  have ha : Real.exp 1 ≤ a := Real.exp_le_exp.mpr (Real.one_le_rpow hL (by norm_num))
  have haX : a ≤ X := by
    rw [← Real.exp_log hX0]
    exact Real.exp_le_exp.mpr (Real.rpow_le_self_of_one_le hL (by norm_num))
  have hp := hprime a X t ha haX
  have he := herr t ht
  have hroot : Real.sqrt ((Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) =
      (Real.log (X : ℝ)) ^ (3 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le]
    norm_num
  simp only [a, Real.log_exp, hroot] at hp
  have hid : (∑ p ∈ mrtLiouvillePrimeTail X,
      characterTwist (1 : DirichletCharacter ℂ q) t p / (p : ℂ)).re =
      ∑ p ∈ mrtLiouvillePrimeTail X, Real.cos (t * Real.log (p : ℝ)) / p := by
    simp only [Complex.re_sum]
    apply sum_congr rfl
    intro p hp
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp, Complex.div_ofReal_re]
    rw [mrt_principal_twist_re hq (mrtPrimeBand_prime hp)
      (mrt_liouville_tail_above_modulus hL hqX hp) t]
  rw [hid]
  change -C - _ ≤ ∑ p ∈ mrtLiouvillePrimeTail X, _ at hp
  linarith



end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_liouville_principal_small_height_oai := @OAI.TwoPointCorrelations.mrt_liouville_principal_small_height_oai
