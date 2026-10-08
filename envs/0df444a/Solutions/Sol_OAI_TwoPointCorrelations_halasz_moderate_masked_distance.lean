-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_moderate_masked_distance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:22:14.505016+00:00
-- url     : https://prove2.me/submissions/9a3ccf61-ce2b-4f5e-b4ef-1584129baa79

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_modFiveThetaInput

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTEulerProducts
namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.ComplexConjugate



lemma mrtArchimedeanTwist_norm (t : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _





/-- Multiplication by a real mask in `[0,1]` can reduce the squared
pretentious distance by at most a factor of two (MRT Lemma A.4(i)). -/
theorem mrt_masked_distance_lower (b twist : ℕ → ℂ) (mask : ℕ → ℝ) (N : ℕ)
    (hb : ∀ p ∈ primesUpTo N, ‖b p‖ ≤ 1)
    (htwist : ∀ p ∈ primesUpTo N, ‖twist p‖ ≤ 1)
    (hmask : ∀ p ∈ primesUpTo N, 0 ≤ mask p ∧ mask p ≤ 1) :
    squaredDistance b twist N ≤
      2 * squaredDistance (fun p => b p * (mask p : ℂ)) twist N := by
  unfold squaredDistance
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.pos
  have hz : ‖b p * conj (twist p)‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact (mul_le_mul (hb p hp) (htwist p hp) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have hx1 : (b p * conj (twist p)).re ≤ 1 := (Complex.re_le_norm _).trans hz
  have hx0 : -1 ≤ (b p * conj (twist p)).re := by
    have := (abs_le.mp (Complex.abs_re_le_norm (b p * conj (twist p)))).1
    linarith
  have he : (b p * (mask p : ℂ) * conj (twist p)).re =
      mask p * (b p * conj (twist p)).re := by
    rw [show b p * (mask p : ℂ) * conj (twist p) =
      (mask p : ℂ) * (b p * conj (twist p)) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hp0.le
  rcases hmask p hp with ⟨hg0, hg1⟩
  by_cases hx : 0 ≤ (b p * conj (twist p)).re
  · have := mul_le_mul_of_nonneg_right hg1 hx
    nlinarith
  · have := mul_nonpos_of_nonneg_of_nonpos hg0 (le_of_lt (lt_of_not_ge hx))
    linarith

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalFactors
namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators




lemma mrtPrimeMask_bounds (P : Finset ℕ) (n : ℕ) :
    0 ≤ mrtPrimeMask P n ∧ mrtPrimeMask P n ≤ 1 := by
  unfold mrtPrimeMask
  split_ifs <;> norm_num














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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPretentiousCenter
namespace OAI

/-! The minimizing twist and the elementary part of MRT Lemma A.4(ii).
Two nearby candidates for the minimum force a lower bound by an explicit
prime cosine sum. Analytic estimates for that prime sum are kept separate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.ComplexConjugate



lemma halasz_twist_sum_norm (t s : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n + mrtArchimedeanTwist s n‖ =
      2 * |Real.cos ((t - s) * Real.log (n : ℝ) / 2)| := by
  let u := (t + s) / 2
  let v := (t - s) * Real.log (n : ℝ) / 2
  have he : mrtArchimedeanTwist t n + mrtArchimedeanTwist s n =
      mrtArchimedeanTwist u n * ((2 : ℂ) * (Real.cos v : ℂ)) := by
    rw [Complex.ofReal_cos, Complex.two_cos, mul_add]
    unfold mrtArchimedeanTwist
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1 <;> congr 1 <;> dsimp [u, v] <;> push_cast <;> ring
  rw [he, norm_mul, mrtArchimedeanTwist_norm, one_mul, norm_mul,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]

theorem halasz_two_twist_distance (F : ℕ → ℂ) (hF : OneBounded F)
    (N : ℕ) (t s : ℝ) :
    2 * (∑ p ∈ primesUpTo N,
      (1 - |Real.cos ((t - s) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
      squaredDistance F (mrtArchimedeanTwist t) N +
        squaredDistance F (mrtArchimedeanTwist s) N := by
  unfold squaredDistance
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  rw [← add_div, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
  have hp0 := (mem_filter.mp hp).2.pos
  have hre : (F p * conj (mrtArchimedeanTwist t p)).re +
      (F p * conj (mrtArchimedeanTwist s p)).re ≤
        ‖mrtArchimedeanTwist t p + mrtArchimedeanTwist s p‖ := by
    calc
      _ = (F p * conj (mrtArchimedeanTwist t p + mrtArchimedeanTwist s p)).re := by
        simp only [map_add, mul_add, Complex.add_re]
      _ ≤ ‖F p * conj (mrtArchimedeanTwist t p + mrtArchimedeanTwist s p)‖ :=
        Complex.re_le_norm _
      _ = ‖F p‖ * ‖mrtArchimedeanTwist t p + mrtArchimedeanTwist s p‖ := by
        rw [norm_mul, Complex.norm_conj]
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) (hF p hp0)
  rw [halasz_twist_sum_norm] at hre
  linarith

lemma halasz_distance_from_minimizer (F : ℕ → ℂ) (hF : OneBounded F)
    (N : ℕ) (t t₁ : ℝ)
    (hmin : squaredDistance F (mrtArchimedeanTwist t₁) N ≤
      squaredDistance F (mrtArchimedeanTwist t) N) :
    (∑ p ∈ primesUpTo N,
      (1 - |Real.cos ((t - t₁) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
        squaredDistance F (mrtArchimedeanTwist t) N := by
  have h := halasz_two_twist_distance F hF N t t₁
  linarith

lemma halasz_prime_cosine_tail_lower (F : ℕ → ℂ) (hF : OneBounded F)
    (N : ℕ) (Y t t₁ : ℝ)
    (hmin : squaredDistance F (mrtArchimedeanTwist t₁) N ≤
      squaredDistance F (mrtArchimedeanTwist t) N) :
    (∑ p ∈ (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)),
      (1 - |Real.cos ((t - t₁) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
        squaredDistance F (mrtArchimedeanTwist t) N := by
  apply le_trans _ (halasz_distance_from_minimizer F hF N t t₁ hmin)
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro p _ _
  exact div_nonneg (sub_nonneg.mpr (Real.abs_cos_le_one _)) (Nat.cast_nonneg p)

lemma halasz_masked_cosine_tail_lower (F : ℕ → ℂ) (hF : OneBounded F)
    (Q : Finset ℕ) (N : ℕ) (Y t t₁ : ℝ)
    (hmin : squaredDistance F (mrtArchimedeanTwist t₁) N ≤
      squaredDistance F (mrtArchimedeanTwist t) N) :
    (∑ p ∈ (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)),
      (1 - |Real.cos ((t - t₁) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
        2 * squaredDistance (mrtMissingCoefficient F Q) (mrtArchimedeanTwist t) N := by
  apply (halasz_prime_cosine_tail_lower F hF N Y t t₁ hmin).trans
  exact mrt_masked_distance_lower F (mrtArchimedeanTwist t) (mrtPrimeMask Q) N
    (fun p hp => hF p (mem_filter.mp hp).2.pos)
    (fun p _ => (mrtArchimedeanTwist_norm t p).le)
    (fun p _ => mrtPrimeMask_bounds Q p)

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

lemma halasz_cosine_defect (x : ℝ) :
    (1 - Real.cos (2 * x)) / 4 ≤ 1 - |Real.cos x| := by
  have hc := Real.abs_cos_le_one x
  have hn := sq_nonneg (1 - |Real.cos x|)
  rw [Real.cos_two_mul]
  nlinarith [sq_abs (Real.cos x)]

lemma halasz_prime_cosine_defect (N : ℕ) (Y t : ℝ) :
    (∑ p ∈ (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)),
      (1 - Real.cos (t * Real.log (p : ℝ))) / (p : ℝ)) ≤
      4 * ∑ p ∈ (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)),
        (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) / (p : ℝ) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p _
  have h := halasz_cosine_defect (t * Real.log (p : ℝ) / 2)
  have he : 2 * (t * Real.log (p : ℝ) / 2) = t * Real.log (p : ℝ) := by ring
  rw [he] at h
  have h' : 1 - Real.cos (t * Real.log (p : ℝ)) ≤
      4 * (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) := by linarith
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h' (Nat.cast_nonneg p)

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

lemma halasz_log_phase_lower (a b t : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (ht : 1 ≤ |t| * Real.log a) :
    Real.log (Real.log b / Real.log a) - 3 ≤
      ∫ x in a..b, oscillatoryReciprocalLog t x := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log (zero_lt_one.trans ha) hab
  have hlb : 0 < Real.log b := hla.trans_le hlab
  have ht0 : 0 < |t| := by
    by_contra hn
    have hz : |t| = 0 := le_antisymm (le_of_not_gt hn) (abs_nonneg t)
    rw [hz, zero_mul] at ht
    norm_num at ht
  have hcos (y : ℝ) : Real.cos (|t| * y) = Real.cos (t * y) := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, neg_mul, Real.cos_neg]
  have htail := (abs_le.mp (cosine_log_tail |t| (Real.log a) (Real.log b)
    ht0 hla hlab ht)).2
  simp_rw [hcos] at htail
  rw [halasz_log_phase_substitution a b t ha hab]
  have hi₁ : IntervalIntegrable (fun y : ℝ => 1 / y) volume (Real.log a) (Real.log b) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlab
    intro y hy
    exact (continuousAt_const.div continuousAt_id (hla.trans_le hy.1).ne').continuousWithinAt
  have hi₂ : IntervalIntegrable (fun y : ℝ => Real.cos (t * y) / y)
      volume (Real.log a) (Real.log b) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlab
    intro y hy
    have hn := (hla.trans_le hy.1).ne'
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun y : ℝ => Real.cos (t * y) / y) y).continuousWithinAt
  have he : (∫ y in Real.log a..Real.log b, (1 - Real.cos (t * y)) / y) =
      Real.log (Real.log b / Real.log a) -
        ∫ y in Real.log a..Real.log b, Real.cos (t * y) / y := by
    rw [← integral_one_div_of_pos hla hlb, ← intervalIntegral.integral_sub hi₁ hi₂]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [he]
  linarith

lemma halasz_prime_band_tail (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    mrtPrimeBand Y N = (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)) := by
  rw [halasz_prime_band_filter]
  ext p
  simp only [mem_filter, mem_Ioc, Nat.floor_natCast, primesUpTo, mem_range]
  rw [Nat.floor_lt hY]
  rw [Nat.lt_succ_iff]
  tauto

theorem ModFiveThetaInput.halasz_prime_phase_lower (hP : ModFiveThetaInput) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ a b t : ℝ,
      Real.exp 1 ≤ a → a ≤ b → 1 ≤ |t| * Real.log a →
      Real.log (Real.log b / Real.log a) - 3 -
          (8 + |t|) * K * Real.exp (-c * Real.sqrt (Real.log a)) / Real.log a ≤
        ∑ p ∈ mrtPrimeBand a b, (1 - Real.cos (t * Real.log p)) / p := by
  obtain ⟨c, K, hc, hK, hh⟩ := hP.halasz_prime_phase_error
  refine ⟨c, K, hc, hK, ?_⟩
  intro a b t ha hab ht
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hi := halasz_log_phase_lower a b t ha1 hab ht
  have he := (abs_le.mp (hh a b t ha hab)).1
  linarith

/-- A finite quantitative repulsion bound, retaining the actual PNT error. -/
theorem ModFiveThetaInput.halasz_masked_phase_lower (hP : ModFiveThetaInput) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ) (N : ℕ) (Y t t₁ : ℝ),
      Real.exp 1 ≤ Y → Y ≤ N → 1 ≤ |t - t₁| * Real.log Y →
      squaredDistance F (mrtArchimedeanTwist t₁) N ≤
        squaredDistance F (mrtArchimedeanTwist t) N →
      (Real.log (Real.log N / Real.log Y) - 3 -
        (8 + |t - t₁|) * K * Real.exp (-c * Real.sqrt (Real.log Y)) / Real.log Y) / 8 ≤
          squaredDistance (mrtMissingCoefficient F Q) (mrtArchimedeanTwist t) N := by
  obtain ⟨c, K, hc, hK, hh⟩ := hP.halasz_prime_phase_lower
  refine ⟨c, K, hc, hK, ?_⟩
  intro F hF Q N Y t t₁ hY hYN ht hmin
  have hY0 : 0 ≤ Y := (Real.exp_pos 1).le.trans hY
  have hphase := hh Y N (t - t₁) hY hYN ht
  rw [halasz_prime_band_tail N Y hY0] at hphase
  have hcos := halasz_prime_cosine_defect N Y (t - t₁)
  have hdist := halasz_masked_cosine_tail_lower F hF Q N Y t t₁ hmin
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszModeratePhase
namespace OAI

/-! Uniform prime-phase repulsion for the moderate-frequency part of MRT
Appendix A. The fourth-root logarithmic coordinate keeps the exponentially
small PNT error separate from the polynomial frequency range. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Topology

lemma halasz_polynomial_phase_error (c K : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, (8 + y ^ 80) * K * Real.exp (-c * y) ≤ 1 := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
  have h80 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (80 : ℕ) c hc
  simp only [Real.rpow_natCast] at h80
  have hh := ((h0.const_mul 8).add h80).mul_const K
  have hlim : Tendsto (fun y : ℝ => (8 + y ^ 80) * K * Real.exp (-c * y))
      atTop (𝓝 0) := by
    convert (preTransparency := .instances) hh using 1
    · ext y
      simp only [Real.rpow_zero, one_mul]
      ring
    · norm_num
  exact (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
    (fun _ h => h.le)

lemma halasz_logarithmic_phase_scale (N : ℕ) (y : ℝ) (hy : 1 < y)
    (hN : Real.log N = y ^ 4) :
    Real.exp 1 ≤ Real.exp (y ^ 2) ∧ Real.exp (y ^ 2) ≤ N ∧
      Real.log (Real.log N / Real.log (Real.exp (y ^ 2))) =
        Real.log (Real.log N) / 2 := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hy2 : 1 < y ^ 2 := by nlinarith
  have hNp : 0 < (N : ℝ) := by
    have hh : 1 < (N : ℝ) := (Real.log_pos_iff (Nat.cast_nonneg N)).mp
      (by rw [hN]; positivity)
    linarith
  refine ⟨Real.exp_le_exp.mpr hy2.le, ?_, ?_⟩
  · rw [← Real.exp_log hNp, hN]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (y ^ 2 - 1)]
  · rw [Real.log_exp, hN, Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    ring

/-- Uniform masked distance repulsion in the moderate frequency range.
The lower bound is independent of the deleted prime set. -/
theorem halasz_moderate_masked_distance_oai :
    ∀ᶠ y : ℝ in atTop, ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ) (N : ℕ) (t t₁ : ℝ), Real.log N = y ^ 4 →
      1 ≤ |t - t₁| * y ^ 2 → |t - t₁| ≤ y ^ 80 →
      squaredDistance F (mrtArchimedeanTwist t₁) N ≤
        squaredDistance F (mrtArchimedeanTwist t) N →
      Real.log (Real.log N) / 16 - 1 / 2 ≤
        squaredDistance (mrtMissingCoefficient F Q) (mrtArchimedeanTwist t) N := by
  obtain ⟨c, K, hc, hK, hphase⟩ := modFiveThetaInput.halasz_masked_phase_lower
  filter_upwards [eventually_gt_atTop (1 : ℝ), halasz_polynomial_phase_error c K hc]
    with y hy herr
  intro F hF Q N t t₁ hN htlo hthi hmin
  obtain ⟨hlo, hhi, hlog⟩ := halasz_logarithmic_phase_scale N y hy hN
  have hh := hphase F hF Q N (Real.exp (y ^ 2)) t t₁ hlo hhi
    (by simpa only [Real.log_exp] using htlo) hmin
  rw [hlog, Real.log_exp, Real.sqrt_sq (by linarith : 0 ≤ y)] at hh
  have hy2 : 1 ≤ y ^ 2 := by nlinarith
  have hnum : (8 + |t - t₁|) * K * Real.exp (-c * y) ≤ 1 := by
    apply le_trans _ herr
    gcongr
  have herr' : (8 + |t - t₁|) * K * Real.exp (-c * y) / y ^ 2 ≤ 1 := by
    exact (div_le_one (by positivity : 0 < y ^ 2)).mpr (hnum.trans hy2)
  linarith


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_moderate_masked_distance_oai := @OAI.TwoPointCorrelations.halasz_moderate_masked_distance_oai
