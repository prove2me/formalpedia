-- Prove2me | solution 1 for OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:55:16.395955+00:00
-- url     : https://prove2.me/submissions/85316ee3-62ff-4226-a20e-c1987d2193c7

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D006
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_constructed_initial_nongiant_priors
import Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_favorable_tail_prime_mass
import Theorems.Thm_OAI_Ostmann_eventual_selected_initial_amplitude

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticErrorRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the fixed-depth arithmetic comparison costs

The polynomial and spectator costs in Section 8 are dominated by the
double-exponential savings. The strict numerical gaps in the manuscript
therefore survive the finite history and equality-pattern sums.
-/

namespace Ostmann

open Filter Asymptotics

theorem arithmetic_exponent_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      C * L ^ n + C * L * Real.exp (a * L) - c * Real.exp (b * L) ≤
        -Real.exp (d * L) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop n hb).const_mul_left C
  have hm : (fun L : ℝ => C * (Real.exp (a * L) * L)) =o[atTop]
      (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_one] using (isLittleO_exp_mul_rpow_of_lt 1 hab).const_mul_left C
  have he : (fun L : ℝ => Real.exp (d * L)) =o[atTop] (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_zero, mul_one] using isLittleO_exp_mul_rpow_of_lt 0 hdb
  have h := ((hp.add hm).add he).bound hc
  filter_upwards [h] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hL
  have hle := (le_abs_self _).trans hL
  nlinarith

theorem arithmetic_error_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ n + C * L * Real.exp (a * L)) *
        Real.exp (-c * Real.exp (b * L)) ≤ Real.exp (-Real.exp (d * L)) := by
  filter_upwards [arithmetic_exponent_absorption a b d C c n hb hab hdb hc] with L hL
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Collision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Elementary collision estimates

These are the finite probability and support-size inequalities used in §2
and in the final collision argument of §3. No analytic estimate is assumed.
-/

namespace Ostmann

open scoped BigOperators

/-- Exact squared distance from uniform probability on a finite support. -/
theorem collision_sub_uniform {α : Type*} (s : Finset α) (μ : α → ℝ)
    (hs : s.Nonempty) (hmass : ∑ x ∈ s, μ x = 1) :
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
      (∑ x ∈ s, μ x ^ 2) - 1 / (s.card : ℝ) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  calc
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
        ∑ x ∈ s, (μ x ^ 2 - (2 / (s.card : ℝ)) * μ x +
          (1 / (s.card : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x ∈ s, μ x ^ 2) -
          2 * (∑ x ∈ s, μ x) / (s.card : ℝ) +
          (s.card : ℝ) * (1 / (s.card : ℝ)) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by rw [hmass]; field_simp; ring

/-- Disjoint nonempty supports occupying at most `p` residues have combined
collision probability at least `4 / p`. -/
theorem four_div_le_inverse_add_inverse {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ p) :
    4 / p ≤ 1 / a + 1 / b := by
  have hp : 0 < p := lt_of_lt_of_le (add_pos ha hb) hab
  have habpos : 0 < a * b := mul_pos ha hb
  have hnum : 4 * (a * b) ≤ p * (a + b) := by
    nlinarith [sq_nonneg (a - b), mul_nonneg (le_of_lt (add_pos ha hb)) (sub_nonneg.mpr hab)]
  apply (div_le_iff₀ hp).mpr
  have hratio : 4 ≤ (p * (a + b)) / (a * b) := (le_div_iff₀ habpos).mpr hnum
  calc
    4 ≤ p * (a + b) / (a * b) := hratio
    _ = (1 / a + 1 / b) * p := by field_simp; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TestFunctions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transfer from collision distance to test functions

The tests need only a bounded squared norm, not a pointwise bound. This is
the Cauchy--Schwarz estimate immediately following Lemma 2.5 in the paper.
-/

namespace Ostmann

open scoped BigOperators

theorem complex_weighted_sum_sq {α : Type*} (s : Finset α)
    (w : α → ℝ) (f : α → ℂ) :
    ‖∑ r ∈ s, (w r : ℂ) * f r‖ ^ 2 ≤
      (∑ r ∈ s, w r ^ 2) * ∑ r ∈ s, ‖f r‖ ^ 2 := by
  have hnorm : ‖∑ r ∈ s, (w r : ℂ) * f r‖ ≤ ∑ r ∈ s, |w r| * ‖f r‖ := by
    calc
      _ ≤ ∑ r ∈ s, ‖(w r : ℂ) * f r‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnonneg : 0 ≤ ∑ r ∈ s, |w r| * ‖f r‖ :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun r => |w r|) (fun r => ‖f r‖)
  simp only [sq_abs] at hCS
  nlinarith [norm_nonneg (∑ r ∈ s, (w r : ℂ) * f r)]

/-- The empirical test error is bounded by the squared distance of the mass
function from the uniform mass on its support, times the test's energy. -/
theorem centered_test_bound {α : Type*} (s : Finset α) (μ : α → ℝ)
    (f : α → ℂ) (p : ℝ) (hf : (∑ r ∈ s, ‖f r‖ ^ 2) ≤ p) :
    ‖∑ r ∈ s, ((μ r - 1 / (s.card : ℝ) : ℝ) : ℂ) * f r‖ ^ 2 ≤
      p * ∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2 := by
  calc
    _ ≤ (∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2) * ∑ r ∈ s, ‖f r‖ ^ 2 :=
      complex_weighted_sum_sq s (fun r => μ r - 1 / (s.card : ℝ)) f
    _ ≤ (∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2) * p :=
      mul_le_mul_of_nonneg_left hf (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := mul_comm _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Probability-normalized additive Fourier identities

These finite identities provide the normalization used in Section 6.
Fourier inversion is the library's discrete Fourier inversion theorem.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem stdAddChar_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  rw [← Complex.inv_eq_conj hn, AddChar.map_neg_eq_inv]

theorem additiveFourier_inversion {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x = ∑ a : ZMod p, additiveFourier f a * ZMod.stdAddChar (a * x) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at hinv
  calc
    f x = (p : ℂ)⁻¹ * ∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a := by
      simpa only [smul_eq_mul] using hinv.symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [additiveFourier]
      ring

theorem additiveFourier_conjugate_coefficient {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    (∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x)) =
      (p : ℂ) * conj (additiveFourier f a) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply]
  simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj, neg_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem additiveFourier_energy {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖f x‖ ^ 2) =
      (p : ℝ) * ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 := by
  have heq : (∑ x : ZMod p, f x * conj (f x)) =
      (p : ℂ) * ∑ a : ZMod p, additiveFourier f a * conj (additiveFourier f a) := by
    calc
      _ = ∑ x : ZMod p, ∑ a : ZMod p,
          additiveFourier f a * ZMod.stdAddChar (a * x) * conj (f x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_mul, ← additiveFourier_inversion]
      _ = ∑ a : ZMod p, additiveFourier f a *
          ∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_comm x a]
        ring
      _ = _ := by
        simp_rw [additiveFourier_conjugate_coefficient]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at heq
  exact_mod_cast heq

/-- Additive Parseval with the manuscript's probability convention. -/
theorem additiveFourier_parseval {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2) =
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [additiveFourier_energy f]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized Fourier transform of the actual centered density -/

namespace Ostmann

open scoped BigOperators

theorem densityFourier_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [densityFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  rw [← Finset.mul_sum, additiveFourier_parseval, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimePartialSummation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partial summation for the reciprocal-prime progression measure

This is the bridge from the published theta estimate (Montgomery--Vaughan,
Corollary 11.20, equations (11.32) and (11.34)) to the interval weights used
in Section 8. The conversion itself is proved here.
-/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem hasDerivAt_primeHarmonicWeight {x : ℝ} (hx : 1 < x) :
    HasDerivAt primeHarmonicWeight (primeHarmonicDerivative x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).inv (mul_ne_zero hx0 hlog)
  change HasDerivAt (fun y : ℝ => (y * Real.log y)⁻¹)
    (-(1 * Real.log x + x * x⁻¹) / (x * Real.log x) ^ 2) x at h
  change HasDerivAt (fun y : ℝ => (y * Real.log y)⁻¹)
    (-(Real.log x + 1) / (x * Real.log x) ^ 2) x
  simpa only [one_mul, mul_inv_cancel₀ hx0] using h

theorem continuousOn_primeHarmonicDerivative {u v : ℝ} (hu : 1 < u) :
    ContinuousOn primeHarmonicDerivative (Set.Icc u v) := by
  intro x hx
  have hx1 : 1 < x := lt_of_lt_of_le hu hx.1
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  exact (((Real.continuousAt_log hx0).add continuousAt_const).neg.div
    ((continuousAt_id.mul (Real.continuousAt_log hx0)).pow 2)
    (pow_ne_zero 2 (mul_ne_zero hx0 hlog))).continuousWithinAt

/-- The exact Abel formula on the actual prime progression, with arbitrary
real endpoints greater than one. -/
theorem reciprocalPrimeInterval_eq_partialSummation (q a : ℕ)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    reciprocalPrimeInterval q a u v =
      primeHarmonicWeight v * primeProgressionTheta q a v -
      primeHarmonicWeight u * primeProgressionTheta q a u -
        ∫ t in Set.Ioc u v, primeHarmonicDerivative t * primeProgressionTheta q a t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc u v) :=
    hasDerivAt_primeHarmonicWeight (lt_of_lt_of_le hu ht.1)
  have hdi : Set.EqOn (deriv primeHarmonicWeight) primeHarmonicDerivative (Set.Icc u v) :=
    fun t ht => (hd t ht).deriv
  have hint : IntegrableOn (deriv primeHarmonicWeight) (Set.Icc u v) :=
    ((continuousOn_primeHarmonicDerivative hu).congr hdi).integrableOn_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul (primeProgressionLog q a)
    (le_of_lt (lt_trans zero_lt_one hu)) huv (fun t ht => (hd t ht).differentiableAt) hint
  have hs : (∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
      primeHarmonicWeight n * primeProgressionLog q a n) = reciprocalPrimeInterval q a u v := by
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : n.Prime ∧ Nat.ModEq q n a
    · have hn1 : (1 : ℝ) < n := by exact_mod_cast h.1.one_lt
      have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn1)
      simp [primeProgressionLog, h, primeHarmonicWeight, mul_inv_rev,
        mul_comm, hlog]
    · simp [primeProgressionLog, h]
  rw [hs] at hab
  change reciprocalPrimeInterval q a u v =
    primeHarmonicWeight v * primeProgressionTheta q a v -
    primeHarmonicWeight u * primeProgressionTheta q a u -
    ∫ t in Set.Ioc u v, deriv primeHarmonicWeight t * primeProgressionTheta q a t at hab
  have hi : (∫ t in Set.Ioc u v, deriv primeHarmonicWeight t * primeProgressionTheta q a t) =
      ∫ t in Set.Ioc u v, primeHarmonicDerivative t * primeProgressionTheta q a t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact congrArg (fun z => z * primeProgressionTheta q a t)
      (hdi (Set.Ioc_subset_Icc_self ht))
  rwa [hi] at hab

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ThetaMainTerm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exceptional theta term and its harmonic density

Differentiating the published theta main term cancels its factor `β`.
The corresponding harmonic density is retained exactly.
-/

namespace Ostmann

open MeasureTheory

theorem continuousOn_thetaMainDensity (φ χ β : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (thetaMainDensity φ χ β) (Set.Icc u v) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hu hx.1)
  exact ((continuousAt_const.sub ((Real.continuousAt_rpow_const x (β - 1)
    (Or.inl hx0)).const_mul χ)).div_const φ).continuousWithinAt

theorem thetaMain_harmonic_integral (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    (∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t) =
      primeHarmonicWeight v * thetaMainTerm φ χ β v -
      primeHarmonicWeight u * thetaMainTerm φ χ β u -
        ∫ t in Set.Ioc u v, primeHarmonicDerivative t * thetaMainTerm φ χ β t := by
  have hi1 : IntervalIntegrable primeHarmonicDerivative volume u v :=
    (continuousOn_primeHarmonicDerivative hu).intervalIntegrable_of_Icc huv
  have hi2 : IntervalIntegrable (thetaMainDensity φ χ β) volume u v :=
    (continuousOn_thetaMainDensity φ χ β (lt_trans zero_lt_one hu)).intervalIntegrable_of_Icc huv
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hasDerivAt_primeHarmonicWeight
      (lt_of_lt_of_le hu ((Set.uIcc_of_le huv) ▸ hx).1))
    (fun x hx => hasDerivAt_thetaMainTerm φ χ β hβ
      (lt_trans zero_lt_one (lt_of_lt_of_le hu ((Set.uIcc_of_le huv) ▸ hx).1))) hi1 hi2
  simpa only [intervalIntegral.integral_of_le huv] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeHarmonicError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative transfer from theta errors to harmonic interval errors -/

namespace Ostmann

open MeasureTheory

/-- Partial summation loses only endpoint weights and the variation of the
harmonic weight. The theta estimate is used on exactly this interval. -/
theorem primeHarmonic_error_le (q a : ℕ) (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v)
    (E B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hθ : ∀ t ∈ Set.Icc u v, |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤ E)
    (hf : ∀ t ∈ Set.Icc u v, |primeHarmonicWeight t| ≤ B)
    (hdf : ∀ t ∈ Set.Icc u v, |primeHarmonicDerivative t| ≤ D) :
    |reciprocalPrimeInterval q a u v -
      ∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t| ≤
        E * (2 * B + (v - u) * D) := by
  let A := primeProgressionTheta q a
  let M := thetaMainTerm φ χ β
  let f := primeHarmonicWeight
  let f' := primeHarmonicDerivative
  have hdint : IntegrableOn f' (Set.Icc u v) :=
    (continuousOn_primeHarmonicDerivative hu).integrableOn_Icc
  have hAint : IntegrableOn (fun t => f' t * A t) (Set.Icc u v) :=
    integrableOn_mul_sum_Icc (primeProgressionLog q a)
      (le_of_lt (lt_trans zero_lt_one hu)) hdint
  have hMcont : ContinuousOn M (Set.Icc u v) := by
    intro x hx
    exact (hasDerivAt_thetaMainTerm φ χ β hβ
      (lt_trans zero_lt_one (lt_of_lt_of_le hu hx.1))).continuousAt.continuousWithinAt
  have hMint : IntegrableOn (fun t => f' t * M t) (Set.Icc u v) :=
    ((continuousOn_primeHarmonicDerivative hu).mul hMcont).integrableOn_Icc
  have hsub : (∫ t in Set.Ioc u v, f' t * A t) -
      (∫ t in Set.Ioc u v, f' t * M t) = ∫ t in Set.Ioc u v, f' t * (A t - M t) := by
    rw [← integral_sub (hAint.mono_set Set.Ioc_subset_Icc_self)
      (hMint.mono_set Set.Ioc_subset_Icc_self)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp
    ring
  have heq : reciprocalPrimeInterval q a u v -
      (∫ t in Set.Ioc u v, f t * thetaMainDensity φ χ β t) =
        f v * (A v - M v) - f u * (A u - M u) -
          ∫ t in Set.Ioc u v, f' t * (A t - M t) := by
    rw [reciprocalPrimeInterval_eq_partialSummation q a hu huv,
      thetaMain_harmonic_integral φ χ β hβ hu huv, ← hsub]
    dsimp [f, f', A, M]
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc u v) : |f t * (A t - M t)| ≤ B * E := by
    rw [abs_mul]
    exact mul_le_mul (hf t ht) (hθ t ht) (abs_nonneg _) hB
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := D * E) (f := fun t => f' t * (A t - M t)) (fun t ht => by
      have ht' : t ∈ Set.Icc u v := Set.Ioc_subset_Icc_self ((Set.uIoc_of_le huv) ▸ ht)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hdf t ht') (hθ t ht') (abs_nonneg _) hD)
  rw [intervalIntegral.integral_of_le huv, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr huv)] at hi
  rw [heq]
  have h1 := norm_sub_le (f v * (A v - M v)) (f u * (A u - M u))
  have h2 := norm_sub_le (f v * (A v - M v) - f u * (A u - M u))
    (∫ t in Set.Ioc u v, f' t * (A t - M t))
  simp only [Real.norm_eq_abs] at h1 h2
  have hv := hbound v ⟨huv, le_rfl⟩
  have hu' := hbound u ⟨le_rfl, huv⟩
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeHarmonicWeightBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit variation cost on a short logarithmic interval -/

namespace Ostmann

open MeasureTheory

theorem primeHarmonicWeight_le {u t : ℝ} (hu : 0 < u)
    (hlogu : 1 ≤ Real.log u) (hut : u ≤ t) :
    |primeHarmonicWeight t| ≤ 1 / u := by
  have ht : 0 < t := hu.trans_le hut
  have hlogt : 1 ≤ Real.log t := hlogu.trans (Real.log_le_log hu hut)
  have hp : u ≤ t * Real.log t := hut.trans (le_mul_of_one_le_right ht.le hlogt)
  rw [primeHarmonicWeight, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  simpa only [one_div] using one_div_le_one_div_of_le hu hp

theorem primeHarmonicDerivative_le {u t : ℝ} (hu : 0 < u)
    (hlogu : 1 ≤ Real.log u) (hut : u ≤ t) :
    |primeHarmonicDerivative t| ≤ 2 / u ^ 2 := by
  have ht : 0 < t := hu.trans_le hut
  have hlogt : 1 ≤ Real.log t := hlogu.trans (Real.log_le_log hu hut)
  have hl : 0 < Real.log t := by linarith
  have hb : (Real.log t + 1) / Real.log t ^ 2 ≤ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    nlinarith [sq_nonneg (Real.log t - 1)]
  have heq : |primeHarmonicDerivative t| =
      ((Real.log t + 1) / Real.log t ^ 2) * (1 / t) ^ 2 := by
    rw [primeHarmonicDerivative, abs_div, abs_neg, abs_of_pos (by linarith),
      abs_of_nonneg (sq_nonneg _)]
    field_simp
  rw [heq]
  calc
    _ ≤ 2 * (1 / t) ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ ≤ 2 * (1 / u) ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hu hut) 2) (by norm_num)
    _ = _ := by ring

/-- A theta error of size `E` on an interval with `v ≤ 3u` costs at most
`6E/u` in the reciprocal-prime measure. -/
theorem primeHarmonic_short_interval_error (q a : ℕ) (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (hlogu : 1 ≤ Real.log u)
    (huv : u ≤ v) (hshort : v ≤ 3 * u) (E : ℝ) (hE : 0 ≤ E)
    (hθ : ∀ t ∈ Set.Icc u v, |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤ E) :
    |reciprocalPrimeInterval q a u v -
      ∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t| ≤ 6 * E / u := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have h := primeHarmonic_error_le q a φ χ β hβ hu huv E (1 / u) (2 / u ^ 2)
    (by positivity) (by positivity) hθ
    (fun t ht => primeHarmonicWeight_le hu0 hlogu ht.1)
    (fun t ht => primeHarmonicDerivative_le hu0 hlogu ht.1)
  refine h.trans ?_
  calc
    _ ≤ E * (2 * (1 / u) + (3 * u - u) * (2 / u ^ 2)) := by gcongr
    _ = 6 * E / u := by field_simp; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ThetaToHarmonic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal-prime estimates derived from the published theta bound -/

namespace Ostmann

open MeasureTheory

/-- The classical theta error on a multiplicative interval transfers with
an absolute factor of eighteen, uniformly in the modulus and residue. -/
theorem theta_to_harmonic_error (q a : ℕ) (φ χ β c C : ℝ) (hβ : β ≠ 0)
    (hc : 0 ≤ c) (hC : 0 ≤ C) {u v : ℝ} (hu : 1 < u)
    (hlogu : 1 ≤ Real.log u) (huv : u ≤ v) (hshort : v ≤ 3 * u)
    (hθ : ∀ t ∈ Set.Icc u v,
      |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤
        C * t * Real.exp (-c * Real.sqrt (Real.log t))) :
    |reciprocalPrimeInterval q a u v -
      ∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t| ≤
        18 * C * Real.exp (-c * Real.sqrt (Real.log u)) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hv0 : 0 < v := hu0.trans_le huv
  let E := C * v * Real.exp (-c * Real.sqrt (Real.log u))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hθ' (t : ℝ) (ht : t ∈ Set.Icc u v) :
      |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤ E := by
    apply (hθ t ht).trans
    dsimp [E]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left ht.2 hC
    · apply Real.exp_le_exp.mpr
      have hs := Real.sqrt_le_sqrt (Real.log_le_log hu0 ht.1)
      nlinarith
    · positivity
    · positivity
  apply (primeHarmonic_short_interval_error q a φ χ β hβ hu hlogu huv hshort E hE hθ').trans
  dsimp [E]
  apply (div_le_iff₀ hu0).mpr
  nlinarith [mul_le_mul_of_nonneg_right hshort
    (mul_nonneg hC (Real.exp_pos (-c * Real.sqrt (Real.log u))).le)]

/-- A log interval of length at most one is a multiplicative interval with
ratio less than three, as required by the uniform partial-summation bound. -/
theorem exp_short_interval_le_three {s t : ℝ} (hst : t ≤ s + 1) :
    Real.exp t ≤ 3 * Real.exp s := by
  calc
    _ ≤ Real.exp (s + 1) := Real.exp_le_exp.mpr hst
    _ = Real.exp s * Real.exp 1 := Real.exp_add s 1
    _ ≤ Real.exp s * 3 := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (Real.exp_pos s).le
    _ = _ := mul_comm _ _

/-- The form used in the finite log-cell partition, before the harmless
change of variables in the main integral. -/
theorem theta_to_log_interval_error (q a : ℕ) (φ χ β c C : ℝ) (hβ : β ≠ 0)
    (hc : 0 ≤ c) (hC : 0 ≤ C) {s t : ℝ} (hs : 1 ≤ s)
    (hst : s ≤ t) (hshort : t ≤ s + 1)
    (hθ : ∀ x ∈ Set.Icc (Real.exp s) (Real.exp t),
      |primeProgressionTheta q a x - thetaMainTerm φ χ β x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ x in Set.Ioc (Real.exp s) (Real.exp t),
        primeHarmonicWeight x * thetaMainDensity φ χ β x| ≤
        18 * C * Real.exp (-c * Real.sqrt s) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  simpa only [Real.log_exp] using theta_to_harmonic_error q a φ χ β c C hβ hc hC
    (Real.one_lt_exp_iff.mpr hs0) (by simpa only [Real.log_exp] using hs)
    (Real.exp_le_exp.mpr hst) (exp_short_interval_le_three hshort) hθ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeLogDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained Page density in logarithmic coordinates -/

namespace Ostmann

open MeasureTheory

/-- The Jacobian cancels the `1/x` part of the harmonic weight. The
exceptional contribution has no extra factor of its zero `β`. -/
theorem thetaMain_log_substitution (φ χ β : ℝ) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    (∫ x in Set.Ioc (Real.exp s) (Real.exp t),
      primeHarmonicWeight x * thetaMainDensity φ χ β x) =
        ∫ y in Set.Ioc s t, primeLogDensity φ χ β y := by
  let g := fun x => primeHarmonicWeight x * thetaMainDensity φ χ β x
  have hg : ContinuousOn g (Real.exp '' Set.uIcc s t) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy0 : 0 < y := hs.trans_le (((Set.uIcc_of_le hst) ▸ hy).1)
    have hexp : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy0
    have hw := (hasDerivAt_primeHarmonicWeight hexp).continuousAt
    have hd : ContinuousAt (thetaMainDensity φ χ β) (Real.exp y) :=
      (continuousAt_const.sub ((Real.continuousAt_rpow_const _ (β - 1)
        (Or.inl (Real.exp_ne_zero y))).const_mul χ)).div_const φ
    exact (hw.mul hd).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (fun y (_ : y ∈ Set.uIcc s t) => Real.hasDerivAt_exp y)
    Real.continuous_exp.continuousOn hg
  calc
    _ = ∫ x in Real.exp s..Real.exp t, g x :=
      (intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hst)).symm
    _ = ∫ y in s..t, (g ∘ Real.exp) y * Real.exp y := hsub.symm
    _ = ∫ y in s..t, primeLogDensity φ χ β y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy0 : 0 < y := hs.trans_le (((Set.uIcc_of_le hst) ▸ hy).1)
      dsimp [g, primeHarmonicWeight, thetaMainDensity, primeLogDensity]
      rw [Real.log_exp, ← Real.exp_mul]
      rw [mul_comm y (β - 1)]
      field_simp
    _ = _ := intervalIntegral.integral_of_le hst

/-- The actual reciprocal-prime interval estimate in logarithmic coordinates,
proved from the precise theta estimate. -/
theorem prime_log_interval_error (q a : ℕ) (φ χ β c C : ℝ) (hβ : β ≠ 0)
    (hc : 0 ≤ c) (hC : 0 ≤ C) {s t : ℝ} (hs : 1 ≤ s)
    (hst : s ≤ t) (hshort : t ≤ s + 1)
    (hθ : ∀ x ∈ Set.Icc (Real.exp s) (Real.exp t),
      |primeProgressionTheta q a x - thetaMainTerm φ χ β x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity φ χ β y| ≤
        18 * C * Real.exp (-c * Real.sqrt s) := by
  have h := theta_to_log_interval_error q a φ χ β c C hβ hc hC hs hst hshort hθ
  rwa [thetaMain_log_substitution φ χ β (lt_of_lt_of_le zero_lt_one hs) hst] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedProgressionInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Precisely stated published inputs for primes in progressions

Reference: H. L. Montgomery and R. C. Vaughan, *Multiplicative Number
Theory I: Classical Theory*, Cambridge Studies in Advanced Mathematics 97,
Chapter 11, DOI 10.1017/CBO9780511618314.013.

`PublishedProgressionInput.theta` is Corollary 11.20, equations (11.32) and
(11.34), p. 381. `complete` specifies the exceptional zero in Theorem 11.3,
p. 360. `unique` is the real-zero specialization of Corollary 11.10 (Page),
p. 369. The positive zero-free constant can be decreased so these use one
constant and the harmless denominator `log (4*q)` throughout.

These are explicit conditional inputs. In particular, no logarithmic
interval estimate or arithmetic comparison is assumed here.
-/

namespace Ostmann

/-- The logarithmic prime estimate is derived by partial summation; it is
not included among the published assumptions. -/
theorem PublishedProgressionInput.local_log_interval (P : PublishedProgressionInput)
    (q a : ℕ) (hq : 1 ≤ q) (ha : a.Coprime q) {s t : ℝ}
    (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (P.localZero q) a) (pageBeta (P.localZero q)) y| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) := by
  apply prime_log_interval_error q a _ _ _ _ _ (ne_of_gt (pageBeta_pos _))
    P.decay_pos.le P.errorConstant_nonneg hs hst hshort
  intro x hx
  apply P.theta q hq a ha x
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have htwo : (2 : ℝ) ≤ Real.exp s := by
    have h := Real.add_one_le_exp s
    linarith
  exact htwo.trans hx.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteProductPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite independent priors used for the arithmetic samples -/

namespace Ostmann

open scoped BigOperators

theorem productPrior_nonneg {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (x : Fin n → A) :
    0 ≤ productPrior μ x := Finset.prod_nonneg fun i _ => hμ i (x i)

theorem productPrior_mass {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i, ∑ a, μ i a = 1) :
    (∑ x : Fin n → A, productPrior μ x) = 1 := by
  unfold productPrior
  rw [← Fintype.prod_sum]
  simp only [hμ, Finset.prod_const_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-divisor budget in the collision argument

A distinct pair of integers at distance at most `X` contributes at most
`log X` to the sum of `log p` over primes at which it collides. This is the
elementary counting step behind the larger-sieve use in §§2–3.
-/

namespace Ostmann

open scoped BigOperators

/-- The off-diagonal prime-collision budget, in the ordered-pair convention. -/
theorem sum_log_congruent_primes_le_of_sub_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hdiff : y - x ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) := by
  have hpos : 0 < y - x := Nat.sub_pos_of_lt hxy
  have hbudget := sum_log_prime_divisors_le (P.filter (fun p => x ≡ y [MOD p])) hpos
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2.dvd')
  exact hbudget.trans (Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast hdiff))

/-- The collision budget for a pair in the initial interval `[0,X]`. -/
theorem sum_log_congruent_primes_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hy : y ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) :=
  sum_log_congruent_primes_le_of_sub_le P hxy ((Nat.sub_le y x).trans hy) hprime

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeLogDensityBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds on the retained density and on discarded real zeros -/

namespace Ostmann

open MeasureTheory

/-- A zero separated from one by `d` contributes at most `exp (-d*s)`
throughout a logarithmic interval beginning at `s ≥ 1`. -/
theorem primeLogDensity_correction_le (φ χ β d : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hd : 0 ≤ d) (hβ : β ≤ 1 - d)
    {s y : ℝ} (hs : 1 ≤ s) (hsy : s ≤ y) :
    |primeLogDensity φ χ β y - primeLogDensity φ 0 1 y| ≤
      Real.exp (-d * s) := by
  have hy : (1 : ℝ) ≤ y := hs.trans hsy
  have hden : (1 : ℝ) ≤ φ * y := by nlinarith
  have hden0 : 0 < φ * y := lt_of_lt_of_le zero_lt_one hden
  have hid : primeLogDensity φ χ β y - primeLogDensity φ 0 1 y =
      -(χ * Real.exp ((β - 1) * y)) / (φ * y) := by
    dsimp [primeLogDensity]
    ring
  rw [hid, abs_div, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hden0]
  have hexp : Real.exp ((β - 1) * y) ≤ Real.exp (-d * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp ((β - 1) * y) / (φ * y) :=
      div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right hχ (Real.exp_pos _).le) hden0.le
    _ ≤ Real.exp (-d * s) / (φ * y) := div_le_div_of_nonneg_right hexp hden0.le
    _ ≤ Real.exp (-d * s) := (div_le_self (Real.exp_pos _).le hden)

theorem primeLogDensity_integral_correction_le (φ χ β d : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hd : 0 ≤ d) (hβ : β ≤ 1 - d)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |(∫ y in Set.Ioc s t, primeLogDensity φ χ β y) -
      (∫ y in Set.Ioc s t, primeLogDensity φ 0 1 y)| ≤ Real.exp (-d * s) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hI (χ β : ℝ) : IntegrableOn (primeLogDensity φ χ β) (Set.Ioc s t) :=
    (continuousOn_primeLogDensity φ χ β hs0).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  rw [← integral_sub (hI χ β) (hI 0 1)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := Real.exp (-d * s))
    (f := fun y => primeLogDensity φ χ β y - primeLogDensity φ 0 1 y)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      exact primeLogDensity_correction_le φ χ β d hφ hχ hd hβ hs
        (((Set.uIoc_of_le hst) ▸ hy).1.le))
  rw [intervalIntegral.integral_of_le hst, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at hi
  exact hi.trans (by nlinarith [Real.exp_pos (-d * s)])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing a smooth cutoff on an actual prime log cell -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem log_mem_of_mem_exp_interval {p : ℕ} {s t : ℝ}
    (hp : p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊) :
    Real.log (p : ℝ) ∈ Set.Ioc s t := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp
  have hexp : Real.exp s < p := Nat.lt_of_floor_lt hlo
  have hp0 : (0 : ℝ) < p := (Real.exp_pos s).trans hexp
  exact ⟨(Real.lt_log_iff_exp_lt hp0).mpr hexp,
    (Real.log_le_iff_le_exp hp0).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp hhi)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single exceptional character for every modulus in a row

Only zeros in Page's common region are retained. Local exceptional zeros
outside that region will be bounded as an error, rather than identified
with a character belonging to a different modulus.
-/

namespace Ostmann

open Classical

theorem selectedPageZero_spec (P : PublishedProgressionInput) (Q : ℕ)
    (e : PrimitiveRealZero) (he : selectedPageZero P Q = some e) :
    e.modulus ≤ Q ∧ 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta := by
  unfold selectedPageZero at he
  split at he
  next hex =>
    have h := Option.some.inj he
    exact h ▸ hex.choose_spec
  next => simp at he

theorem selectedPageZero_eq (P : PublishedProgressionInput) (Q : ℕ)
    (hQ : 2 ≤ Q) (e : PrimitiveRealZero) (hmod : e.modulus ≤ Q)
    (hnear : 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta) :
    selectedPageZero P Q = some e := by
  have hex : ∃ f : PrimitiveRealZero, f.modulus ≤ Q ∧
      1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ f.beta := ⟨e, hmod, hnear⟩
  have heq := P.unique Q hQ hex.choose e hex.choose_spec.1 hmod hex.choose_spec.2 hnear
  unfold selectedPageZero
  rw [dite_eq_left hex, heq]

theorem page_region_mono (P : PublishedProgressionInput) {q Q : ℕ}
    (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    1 - P.kappa / Real.log (4 * (q : ℝ)) ≤
      1 - P.kappa / Real.log (4 * (Q : ℝ)) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hlog : Real.log (4 * (q : ℝ)) ≤ Real.log (4 * (Q : ℝ)) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 4 hqQ)
  have hdiv := div_le_div_of_nonneg_left P.kappa_pos.le hpos hlog
  linarith

theorem localZero_eq_of_selected (P : PublishedProgressionInput) {q Q : ℕ}
    (hq : 1 ≤ q) (hqQ : q ≤ Q) (e : PrimitiveRealZero)
    (he : selectedPageZero P Q = some e) (hd : e.modulus ∣ q) :
    P.localZero q = some e :=
  P.complete q hq e hd
    ((page_region_mono P hq hqQ).trans (selectedPageZero_spec P Q e he).2)

/-- Every local correction either equals the restriction of the same global
Page correction, or is a zero lying strictly outside the common region.
In the latter case the global correction is absent from that modulus. -/
theorem localZero_selected_alternative (P : PublishedProgressionInput) {q Q : ℕ}
    (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    P.localZero q = pageAtModulus q (selectedPageZero P Q) ∨
      ∃ e : PrimitiveRealZero, P.localZero q = some e ∧
        e.beta < 1 - P.kappa / Real.log (4 * (Q : ℝ)) ∧
        pageAtModulus q (selectedPageZero P Q) = none := by
  cases hl : P.localZero q with
  | none =>
    left
    cases hg : selectedPageZero P Q with
    | none => simp [pageAtModulus]
    | some e =>
      by_cases hd : e.modulus ∣ q
      · have hc := localZero_eq_of_selected P hq hqQ e hg hd
        rw [hl] at hc
        contradiction
      · simp [pageAtModulus, hd]
  | some e =>
    have hd := P.divides q e hl
    by_cases hn : 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta
    · left
      have he := selectedPageZero_eq P Q hQ e
        ((Nat.le_of_dvd (by omega) hd).trans hqQ) hn
      simp [he, pageAtModulus, hd]
    · right
      refine ⟨e, rfl, lt_of_not_ge hn, ?_⟩
      cases hg : selectedPageZero P Q with
      | none => simp [pageAtModulus]
      | some f =>
        by_cases hf : f.modulus ∣ q
        · have hc := localZero_eq_of_selected P hq hqQ f hg hf
          rw [hl] at hc
          have hef := Option.some.inj hc
          exact False.elim (hn (hef ▸ (selectedPageZero_spec P Q f hg).2))
        · simp [pageAtModulus, hf]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_UniformPrimeProgressions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform prime intervals with one retained Page character

The second error below accounts for local exceptional zeros outside Page's
common region. This derives simultaneous compatibility across moduli from
the published zero uniqueness, rather than assuming compatibility of the
short-interval estimates.
-/

namespace Ostmann

open MeasureTheory

theorem PublishedProgressionInput.uniform_log_interval (P : PublishedProgressionInput)
    {q Q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
        (pageBeta (pageAtModulus q (selectedPageZero P Q))) y| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) +
        Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ))) := by
  have hlocal := P.local_log_interval q a hq ha hs hst hshort
  rcases localZero_selected_alternative P hQ hq hqQ with heq | ⟨e, he, hfar, hn⟩
  · rw [heq] at hlocal
    exact hlocal.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hφ : (1 : ℝ) ≤ Nat.totient q := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
    have hlog : 0 < Real.log (4 * (Q : ℝ)) := by
      apply Real.log_pos
      have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith
    have hcorr := primeLogDensity_integral_correction_le (Nat.totient q)
      (pageCoefficient (some e) a) e.beta (P.kappa / Real.log (4 * (Q : ℝ)))
      hφ (pageCoefficient_abs_le_one _ _) (div_nonneg P.kappa_pos.le hlog.le)
      hfar.le hs hst hshort
    rw [he] at hlocal
    rw [hn]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (reciprocalPrimeInterval q a (Real.exp s) (Real.exp t))
      (∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (some e) a) e.beta y)
      (∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q) 0 1 y)
    simp only [Real.norm_eq_abs] at htri
    have hbound := htri.trans (add_le_add hlocal hcorr)
    have hexp : Real.exp (-(P.kappa / Real.log (4 * (Q : ℝ))) * s) =
        Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ))) := by
      congr 1
      ring
    rw [hexp] at hbound
    exact hbound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellUpper
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform upper mass bound on a logarithmic prime cell -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem sum_primeLogCellSet_reciprocal (q a : ℕ) (s t : ℝ) :
    (∑ p ∈ primeLogCellSet q a s t, (p : ℝ)⁻¹) =
      reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) := by
  simp only [primeLogCellSet, Finset.sum_filter, reciprocalPrimeInterval]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete equal-mesh log cells and unit residues -/

namespace Ostmann

open scoped Classical

theorem mem_primeLogCellSet_iff {q a p : ℕ} {s t : ℝ} :
    p ∈ primeLogCellSet q a s t ↔
      p.Prime ∧ Nat.ModEq q p a ∧ Real.log (p : ℝ) ∈ Set.Ioc s t := by
  constructor
  · intro hp
    obtain ⟨hI, hprime, hres⟩ := Finset.mem_filter.mp hp
    exact ⟨hprime, hres, log_mem_of_mem_exp_interval hI⟩
  · rintro ⟨hprime, hres, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hprime, hres⟩
    · exact (Nat.floor_lt (Real.exp_pos s).le).mpr ((Real.lt_log_iff_exp_lt hp0).mp hlo)
    · exact (Nat.le_floor_iff (Real.exp_pos t).le).mpr ((Real.log_le_iff_le_exp hp0).mp hhi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_nonneg (P Q : Finset ℕ) (p : P) :
    0 ≤ primeSubsetPrior P Q p := by
  unfold primeSubsetPrior
  split_ifs
  · exact div_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact le_rfl

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Symmetries of the mixed Fourier bound

Conjugation and multiplication of the field argument by a unit preserve
both the energy hypothesis and the mixed character/Fourier bound. These
are the orientation changes used by the bottom pairs.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_conj {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => conj (f x)) a = conj (additiveFourier f (-a)) := by
  simp only [additiveFourier_apply, map_mul, map_inv₀, map_natCast, map_sum,
    stdAddChar_conj, mul_neg, neg_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ProgressionErrorRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two arithmetic progression precision scales

The published square-root-log theta error is sufficient on both rows of
Section 8. The discarded Page zeros have the stronger exponent `a₀ - μ`.
-/

namespace Ostmann

open Filter

theorem constant_mul_double_exp_le (K c b d : ℝ) (hK : 0 ≤ K)
    (hc : 0 < c) (hb : 0 < b) (hdb : d < b) :
    ∀ᶠ L : ℝ in atTop, K * Real.exp (-c * Real.exp (b * L)) ≤
      Real.exp (-Real.exp (d * L)) := by
  filter_upwards [arithmetic_error_absorption 0 b d K c 0 hb hb hdb hc,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  apply le_trans _ hL
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  apply hKe.trans
  apply Real.exp_le_exp.mpr
  simp only [pow_zero, mul_one, zero_mul, Real.exp_zero]
  nlinarith

theorem sqrt_ge_log_scale {a L s : ℝ} (hs : Real.exp (a * L) ≤ s) :
    Real.exp ((a / 2) * L) ≤ Real.sqrt s := by
  have h := Real.sqrt_le_sqrt hs
  rw [← Real.exp_half] at h
  exact (congrArg Real.exp (by ring : (a / 2) * L = a * L / 2)).trans_le h

theorem page_gap_ge_log_scale (κ a μ L H s : ℝ) (hκ : 0 ≤ κ)
    (hH0 : 0 < H) (hH : H ≤ 2 * Real.exp (μ * L)) (hs : Real.exp (a * L) ≤ s) :
    (κ / 2) * Real.exp ((a - μ) * L) ≤ κ * s / H := by
  apply (le_div_iff₀ hH0).mpr
  calc
    _ ≤ ((κ / 2) * Real.exp ((a - μ) * L)) * (2 * Real.exp (μ * L)) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ = κ * Real.exp (a * L) := by
      have he : Real.exp ((a - μ) * L) * Real.exp (μ * L) = Real.exp (a * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = κ * (Real.exp ((a - μ) * L) * Real.exp (μ * L)) := by ring
        _ = _ := by rw [he]
    _ ≤ κ * s := mul_le_mul_of_nonneg_left hs hκ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_WeightedProgressionRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical error budgets for the weighted giant comparison -/

namespace Ostmann
open Filter

/-- The explicit published-input error bound itself has the required uniform
rate, before a continuous weight or residue-cell count is inserted. -/
theorem PublishedProgressionInput.log_interval_budget_rate (P : PublishedProgressionInput)
    (a₀ μ δ : ℝ) (hδa : δ < a₀ / 2) (hδμ : δ < a₀ - μ)
    (ha : 0 < a₀) (haμ : 0 < a₀ - μ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp (μ * L) →
      ∀ u : ℝ, Real.exp (a₀ * L) ≤ u →
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) ≤
          2 * Real.exp (-Real.exp (δ * L)) := by
  filter_upwards [constant_mul_double_exp_le (18 * P.errorConstant) P.decay (a₀ / 2) δ
      (mul_nonneg (by norm_num) P.errorConstant_nonneg) P.decay_pos (by positivity) hδa,
    constant_mul_double_exp_le 1 (P.kappa / 2) (a₀ - μ) δ (by norm_num)
      (div_pos P.kappa_pos (by norm_num)) haμ hδμ] with L htheta hpage
  intro Q hQ hH u hu
  have hlog : 0 < Real.log (4 * (Q : ℝ)) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have ht : 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) ≤
      Real.exp (-Real.exp (δ * L)) := by
    apply le_trans _ htheta
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) P.errorConstant_nonneg)
    apply Real.exp_le_exp.mpr
    nlinarith [sqrt_ge_log_scale hu, P.decay_pos]
  have hp : Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) ≤
      Real.exp (-Real.exp (δ * L)) := by
    apply le_trans _ (by simpa only [one_mul] using hpage)
    apply Real.exp_le_exp.mpr
    have hg := page_gap_ge_log_scale P.kappa a₀ μ L (Real.log (4 * (Q : ℝ))) u
      P.kappa_pos.le hlog hH hu
    simpa only [neg_mul, neg_div] using neg_le_neg hg
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantLogMeasures
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual ideal giant measures, including the retained Page density -/

namespace Ostmann
open MeasureTheory
open scoped ENNReal

theorem intervalDensityMeasure_mass (u v : ℝ) (ρ : ℝ → ℝ)
    (hρ : IntegrableOn ρ (Set.Ioc u v)) (hpos : ∀ x ∈ Set.Ioc u v, 0 ≤ ρ x) :
    (intervalDensityMeasure u v ρ).real Set.univ = ∫ x in Set.Ioc u v, ρ x := by
  have hp : ∀ᵐ x ∂volume.restrict (Set.Ioc u v), 0 ≤ ρ x :=
    ae_restrict_of_forall_mem measurableSet_Ioc hpos
  rw [Measure.real, intervalDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hρ hp,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hp)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellMeasure
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact atomic measure of a harmonic prime cell -/

namespace Ostmann
open MeasureTheory Filter
open scoped BigOperators ENNReal BoundedContinuousFunction

theorem primeLogCellMeasure_integral (q a : ℕ) (u v : ℝ) (f : ℝ →ᵇ ℂ) :
    (∫ t, f t ∂primeLogCellMeasure q a u v) =
      ∑ p ∈ primeLogCellSet q a u v, f (Real.log p) * ((p : ℝ)⁻¹ : ℂ) := by
  unfold primeLogCellMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul, mul_comm]
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  · intro p _
    exact f.integrable _

theorem primeLogCellMeasure_mass (q a : ℕ) (u v : ℝ) :
    (primeLogCellMeasure q a u v).real Set.univ =
      ∑ p ∈ primeLogCellSet q a u v, (p : ℝ)⁻¹ := by
  have h := primeLogCellMeasure_integral q a u v (BoundedContinuousFunction.const ℝ (1 : ℂ))
  simp only [BoundedContinuousFunction.const_apply, integral_const, Complex.real_smul,
    mul_one, one_mul] at h
  exact_mod_cast h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkPrimeCellMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mass control for the normalized union of actual prime cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem primeLogCell_page_mass_error (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    |(primeLogCellMeasure q a u v).real Set.univ -
      (primeGiantMeasure P Q q a u v).real Set.univ| ≤ bulkPrimeErrorFactor P Q u := by
  rw [primeLogCellMeasure_mass, sum_primeLogCellSet_reciprocal,
    primeGiantMeasure, intervalDensityMeasure_mass u v _
      (selectedPrimeLogDensity_integrable P Q q a u v (by linarith))
      (selectedPrimeLogDensity_nonneg P Q q a u v (by linarith))]
  have h := P.uniform_log_interval hQ hq hqQ ha hu huv hshort
  exact h.trans (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * Real.exp (-u)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem residueVariance_pos {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) : 0 < residueVariance S := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hd : 0 < residueDensity S := div_pos (by exact_mod_cast hS.card_pos) hp
  have hd1 : residueDensity S < 1 := (div_lt_one hp).mpr (by exact_mod_cast hSp)
  exact mul_pos hd (sub_pos.mpr hd1)

theorem normalizedResidueIndicator_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, normalizedResidueIndicator S x) = 0 := by
  simp only [normalizedResidueIndicator, ← Complex.ofReal_sum, ← Finset.sum_div,
    centeredDensity_sum, zero_div, Complex.ofReal_zero]

theorem normalizedResidueTransform_zero {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    normalizedResidueTransform S 0 = 0 := by
  simp only [normalizedResidueTransform, densityFourier, additiveFourier_apply,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, normalizedResidueIndicator_sum]

theorem normalizedResidueTransform_neg {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p)) (x : ZMod p) :
    normalizedResidueTransform S (-x) = conj (normalizedResidueTransform S x) := by
  have hreal : (fun y => conj (normalizedResidueIndicator S y)) = normalizedResidueIndicator S := by
    funext y
    simp only [normalizedResidueIndicator, Complex.conj_ofReal]
  have hh := additiveFourier_conj (normalizedResidueIndicator S) (-x)
  rw [hreal, neg_neg] at hh
  simp only [normalizedResidueTransform, densityFourier, map_mul, Complex.conj_ofReal]
  rw [hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicBoxMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The true harmonic mass of the reassembled bulk boxes -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem pageAtModulus_one (z : Option PrimitiveRealZero) : pageAtModulus 1 z = none := by
  cases z with
  | none => rfl
  | some e =>
    simp [pageAtModulus, e.modulus_ne_one]

theorem selectedPrimeLogDensity_one (P : PublishedProgressionInput) (Q a : ℕ) (x : ℝ) :
    selectedPrimeLogDensity P Q 1 a x = x⁻¹ := by
  simp [selectedPrimeLogDensity, primeLogDensity, pageAtModulus_one, pageCoefficient]

theorem primeGiantMeasure_one_mass (P : PublishedProgressionInput) (Q a : ℕ)
    (u v : ℝ) (hu : 0 < u) :
    (primeGiantMeasure P Q 1 a u v).real Set.univ = ∫ x in Set.Ioc u v, (x : ℝ)⁻¹ := by
  rw [primeGiantMeasure, intervalDensityMeasure_mass u v _
    (selectedPrimeLogDensity_integrable P Q 1 a u v hu)
    (selectedPrimeLogDensity_nonneg P Q 1 a u v hu.le)]
  simp only [selectedPrimeLogDensity_one]

theorem harmonic_box_mass_log (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    (∫ x in Set.Ioc u v, (x : ℝ)⁻¹) = Real.log (v / u) := by
  rw [← intervalIntegral.integral_of_le huv, integral_inv_of_pos hu (hu.trans_le huv)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_BulkProgressionRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full bulk progression error, including derivative cuts and endpoints -/

namespace Ostmann
open Filter

/-- The Section 8 bulk row absorbs variable polynomial-cut counts, residue
counts, and the complete smooth budget. No fixed bound on the number of roots
is needed: those costs are all included in `V`. -/
theorem PublishedProgressionInput.bulk_full_progression_budget_rate (P : PublishedProgressionInput)
    (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      ∀ u V : ℝ, Real.exp ((39 / 10000 : ℝ) * L) ≤ u →
      V ≤ Real.exp (C * L ^ d + C * L * Real.exp ((14 / 10000 : ℝ) * L)) →
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)) ≤
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
  filter_upwards [P.log_interval_budget_rate (39 / 10000) (12 / 10000) (18 / 10000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_error_absorption (14 / 10000) (18 / 10000) (13 / 10000) C 1 d
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    constant_mul_double_exp_le 4 1 (13 / 10000) (125 / 100000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L hP hcost hfour hL
  intro Q hQ hlog u V hu hV
  have hsmall : Real.exp (-u) ≤ Real.exp (-Real.exp ((18 / 10000 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans hu
  have he := hP Q hQ hlog u hu
  have hC := P.errorConstant_nonneg
  have hn : 0 ≤ 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
      Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u) := by positivity
  have htotal : 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
      Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u) ≤
      4 * Real.exp (-Real.exp ((18 / 10000 : ℝ) * L)) := by linarith
  calc
    _ ≤ Real.exp (C * L ^ d + C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        (4 * Real.exp (-Real.exp ((18 / 10000 : ℝ) * L))) :=
      mul_le_mul hV htotal hn (Real.exp_pos _).le
    _ = 4 * (Real.exp (C * L ^ d + C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        Real.exp (-Real.exp ((18 / 10000 : ℝ) * L))) := by ring
    _ ≤ 4 * Real.exp (-Real.exp ((13 / 10000 : ℝ) * L)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [one_mul, neg_mul] using hcost
    _ ≤ _ := by simpa only [one_mul, neg_mul] using hfour

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkWeightedErrorBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting the actual cells and residues in the bulk comparison error -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem bulkPrimeErrorFactor_antitone (P : PublishedProgressionInput) {Q : ℕ} (hQ : 2 ≤ Q)
    {u v : ℝ} (huv : u ≤ v) : bulkPrimeErrorFactor P Q v ≤ bulkPrimeErrorFactor P Q u := by
  have hlog : 0 < Real.log (4 * (Q : ℝ)) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hroot : -P.decay * Real.sqrt v ≤ -P.decay * Real.sqrt u :=
    mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt huv) (neg_nonpos.mpr P.decay_pos.le)
  have hpage : -P.kappa * v / Real.log (4 * (Q : ℝ)) ≤
      -P.kappa * u / Real.log (4 * (Q : ℝ)) := by
    apply div_le_div_of_nonneg_right _ hlog.le
    exact mul_le_mul_of_nonpos_left huv (neg_nonpos.mpr P.kappa_pos.le)
  unfold bulkPrimeErrorFactor
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hroot)
        (mul_nonneg (by norm_num) P.errorConstant_nonneg))
      (Real.exp_le_exp.mpr hpage))
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg huv)) (by norm_num))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OneSidedDecayBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated long/short scales absorb the one-sided losses -/

namespace Ostmann

open Filter

theorem eventual_polynomial_log_budget (C z α ε : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      C * (1 + m) ^ d ≤ ε * Real.exp (α * L) := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop d hα).const_mul_left
    (C * (z + 1) ^ d)).bound hε
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hlarge hL m hm hmL
  have hx : 1 + m ≤ (z + 1) * L := by nlinarith
  have hp : (1 + m) ^ d ≤ ((z + 1) * L) ^ d := pow_le_pow_left₀ (by linarith) hx d
  have hlarge' : C * (z + 1) ^ d * L ^ d ≤ ε * Real.exp (α * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C * (z + 1) ^ d * L ^ d),
      abs_of_pos (Real.exp_pos _)] using hlarge
  calc
    _ ≤ C * (((z + 1) * L) ^ d) := mul_le_mul_of_nonneg_left hp hC
    _ = C * (z + 1) ^ d * L ^ d := by rw [mul_pow]; ring
    _ ≤ _ := hlarge'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorBulkScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The even bulk size and the accumulated giant loss in Section 9 -/

namespace Ostmann
open Filter
open scoped BigOperators

theorem spectatorBulkCount_lower (k : ℕ) (L : ℝ) :
    (k : ℝ) ^ 4 * L - 2 < (spectatorBulkCount k L : ℝ) := by
  have h := Nat.sub_one_lt_floor ((k : ℝ) ^ 4 * L / 2)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_upper (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L := by
  have h := Nat.floor_le (show 0 ≤ (k : ℝ) ^ 4 * L / 2 by positivity)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_half (k : ℕ) (L : ℝ)
    (hL : 4 ≤ (k : ℝ) ^ 4 * L) :
    (k : ℝ) ^ 4 * L / 2 ≤ (spectatorBulkCount k L : ℝ) := by
  linarith [spectatorBulkCount_lower k L]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards compensation-center construction of equation (7.4) -/

namespace Ostmann

theorem movingCompensationTargets_sum (J : ℝ) (ds : List ℝ) :
    J + (movingCompensationTargets J ds).sum =
      (2 : ℝ) ^ ds.length * J - movingCompensationTargetError ds := by
  induction ds with
  | nil => simp only [movingCompensationTargets, List.sum_nil, List.length_nil,
      pow_zero, one_mul, movingCompensationTargetError, sub_zero, add_zero]
  | cons d ds ih =>
    simp only [movingCompensationTargets, List.sum_cons, List.length_cons,
      movingCompensationTargetError, pow_succ]
    linarith

theorem movingCompensationTargetError_bounds (B : ℝ) (ds : List ℝ)
    (h : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    0 ≤ movingCompensationTargetError ds ∧
      movingCompensationTargetError ds ≤ ((2 : ℝ) ^ ds.length - 1) * B := by
  induction ds with
  | nil => simp only [movingCompensationTargetError, List.length_nil, pow_zero,
      sub_self, zero_mul, le_refl, and_self]
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht := ih (fun x hx => h x (by simp only [List.mem_cons]; exact Or.inr hx))
    simp only [movingCompensationTargetError, List.length_cons, pow_succ]
    constructor <;> linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every prescribed compensation target lies in the small-prime range -/

namespace Ostmann
open Filter

theorem movingCompensationTargets_mem_bounds (J B : ℝ) (ds : List ℝ)
    (hJ : 0 ≤ J) (hB : 0 ≤ B) (hd : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    ∀ w ∈ movingCompensationTargets J ds,
      J - 2 ^ ds.length * B ≤ w ∧ w ≤ 2 ^ ds.length * J := by
  induction ds with
  | nil => simp [movingCompensationTargets]
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e ∧ e ≤ B := fun e he => hd e (by simp [he])
    have herror := movingCompensationTargetError_bounds B ds hds
    have hsum := movingCompensationTargets_sum J ds
    have hp : (1 : ℝ) ≤ 2 ^ ds.length := one_le_pow₀ (by norm_num)
    have hpJ := mul_le_mul_of_nonneg_right hp hJ
    have hpB : 0 ≤ (2 : ℝ) ^ ds.length * B := by positivity
    have hpJ0 : 0 ≤ (2 : ℝ) ^ ds.length * J := by positivity
    intro w hw
    simp only [movingCompensationTargets, List.mem_cons] at hw
    simp only [List.length_cons, pow_succ]
    rcases hw with rfl | hw
    · constructor <;> nlinarith only [hsum, herror.1, herror.2, hd0.1, hd0.2, hpJ, hpB, hpJ0]
    · obtain ⟨hl, hu⟩ := ih hds w hw
      constructor <;> nlinarith only [hl, hu, hpB, hpJ0]

theorem eventual_moving_compensation_range (k : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ (J : ℝ) (ds : List ℝ), ds.length ≤ k →
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) →
      (∀ d ∈ ds, 0 ≤ d ∧ d ≤ B * L) →
      ∀ w ∈ movingCompensationTargets J ds,
        Real.exp ((1 / 100 : ℝ) * L) ≤ w / 4 ∧
        w / 4 ≤ Real.exp ((105 / 10000 : ℝ) * L) := by
  let C := (2 : ℝ) ^ k * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht : Tendsto (fun L : ℝ => Real.exp ((5 / 10000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [arithmetic_exponent_absorption 0 (1 / 100) 0 C 8 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ht.eventually (eventually_ge_atTop (8 * (2 : ℝ) ^ k)),
    eventually_ge_atTop (0 : ℝ)] with L hgap hratio hL
  intro J ds hlen hJlo hJhi hd w hw
  have hJ : 0 ≤ J := (by positivity : 0 ≤ 16 * Real.exp ((1 / 100 : ℝ) * L)).trans hJlo
  have hpow : (2 : ℝ) ^ ds.length ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hlen
  have hpowB := mul_le_mul_of_nonneg_right hpow (mul_nonneg hB hL)
  have hpowJ := mul_le_mul_of_nonneg_right hpow hJ
  obtain ⟨hl, hu⟩ := movingCompensationTargets_mem_bounds J (B * L) ds hJ (mul_nonneg hB hL) hd w hw
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one] at hgap
  have hCL : 0 ≤ C * L := mul_nonneg hC hL
  have hcost : (2 : ℝ) ^ k * (B * L) ≤ 8 * Real.exp ((1 / 100 : ℝ) * L) := by
    dsimp only [C] at hgap hCL
    nlinarith only [hgap, hCL]
  constructor
  · nlinarith only [hl, hpowB, hcost, hJlo, Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  · have hscale := mul_le_mul_of_nonneg_right hratio
      (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    have heq : Real.exp ((5 / 10000 : ℝ) * L) * Real.exp ((1 / 100 : ℝ) * L) =
        Real.exp ((105 / 10000 : ℝ) * L) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hscale
    have hJbound := mul_le_mul_of_nonneg_left hJhi (by positivity : 0 ≤ (2 : ℝ) ^ k)
    nlinarith only [hu, hpowJ, hscale, hJbound]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationGapList
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed normalized gaps in the backwards target recursion -/

namespace Ostmann
open Filter

theorem movingCompensationGapRate_nonneg (k : ℕ) (hk : 0 < k)
    (BD Bz : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    0 ≤ movingCompensationGapRate k BD Bz := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1
  have hzlog := Real.log_nonneg hz
  have h2log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold movingCompensationGapRate
  positivity

theorem movingCompensationGaps_bounds (k : ℕ) (hk : 0 < k)
    (BD Bz L : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hL : 0 ≤ L) :
    ∀ d ∈ movingCompensationGaps k BD Bz L,
      0 ≤ d ∧ d ≤ movingCompensationGapRate k BD Bz * L := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  have hr : (0 : ℝ) < 2 ^ (i : ℕ) := by positivity
  have heq : spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ))
      (spectatorBulkCount k L) / (2 : ℝ) ^ (i : ℕ) =
      (BD + Bz * Real.log ((k : ℝ) ^ 4) +
        (2 / 5 : ℝ) * (i : ℕ) * Real.log 2) * (spectatorBulkCount k L : ℝ) := by
    unfold spectatorStepGap
    simp only [Real.log_pow]
    field_simp [hr.ne']
  rw [heq]
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hk)
  have hzlog := Real.log_nonneg hz
  have h2log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hi : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast i.isLt.le
  have hc : 0 ≤ BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * (i : ℕ) * Real.log 2 := by positivity
  have hc' : BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * (i : ℕ) * Real.log 2 ≤
      BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * k * Real.log 2 := by
    nlinarith only [hi, h2log]
  refine ⟨mul_nonneg hc (Nat.cast_nonneg _), ?_⟩
  have h1 := mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg (spectatorBulkCount k L) (α := ℝ))
  have h2 := mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL)
    (hc.trans hc')
  dsimp [movingCompensationGapRate]
  nlinarith only [h1, h2]

theorem eventual_prescribed_compensation_range (k : ℕ) (hk : 0 < k)
    (BD Bz : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ J : ℝ,
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) →
      ∀ w ∈ movingCompensationTargets J (movingCompensationGaps k BD Bz L),
        Real.exp ((1 / 100 : ℝ) * L) ≤ w / 4 ∧
        w / 4 ≤ Real.exp ((105 / 10000 : ℝ) * L) := by
  filter_upwards [eventual_moving_compensation_range k (movingCompensationGapRate k BD Bz)
      (movingCompensationGapRate_nonneg k hk BD Bz hBD hBz),
    eventually_ge_atTop (0 : ℝ)] with L htarget hL
  intro J hJlo hJhi
  exact htarget J (movingCompensationGaps k BD Bz L)
    (by simp) hJlo hJhi (movingCompensationGaps_bounds k hk BD Bz L hBD hBz hL)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProtectedTarget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The protected target from the actual initial window -/

namespace Ostmann
open Filter

theorem eventual_protected_target_error (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ totalGap td : ℝ,
      0 ≤ totalGap → totalGap ≤ C * L →
      0 ≤ td → td ≤ C * L * Real.exp ((1 / 1000 : ℝ) * L) →
      |totalGap - 2 * td| ≤ Real.exp ((1 / 100 : ℝ) * L) := by
  filter_upwards [arithmetic_exponent_absorption (1 / 1000) (1 / 100) 0 (2 * C) 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with L hrate
  intro totalGap td hgap0 hgap htd0 htd
  simp only [pow_one, one_mul, zero_mul, Real.exp_zero] at hrate
  rw [abs_le]
  constructor <;> nlinarith only [hgap0, hgap, htd0, htd, hrate]

theorem eventual_protected_cell_target_range :
    ∀ᶠ L : ℝ in atTop, ∀ J cb : ℝ,
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) →
      0 ≤ cb → cb ≤ J / 4 →
      Real.exp ((1 / 100 : ℝ) * L) ≤ (J - cb) / 6 ∧
      (J - cb) / 6 ≤ Real.exp ((105 / 10000 : ℝ) * L) := by
  have ht : Tendsto (fun L : ℝ => Real.exp ((5 / 10000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [ht.eventually (eventually_ge_atTop (8 : ℝ))] with L hratio
  intro J cb hJlo hJhi hcb0 hcb
  have hs := mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg ((1 / 100 : ℝ) * L))
  have heq : Real.exp ((5 / 10000 : ℝ) * L) * Real.exp ((1 / 100 : ℝ) * L) =
      Real.exp ((105 / 10000 : ℝ) * L) := by rw [← Real.exp_add]; congr 1; ring
  rw [heq] at hs
  constructor <;> nlinarith only [hJlo, hJhi, hcb0, hcb, hs,
    Real.exp_nonneg ((1 / 100 : ℝ) * L)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Basic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sets in Ostmann's inverse Goldbach problem

We use `ℕ` for the manuscript's nonnegative integers. The threshold convention
uses `N ≤ n`; changing finitely many initial values does not affect it.
-/

namespace Ostmann

open scoped symmDiff

/-- Each sufficiently large sum of elements of the summands is prime. -/
theorem EventuallyPrimeSumset.prime_add {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ a ∈ A, ∀ b ∈ B, N ≤ a + b → (a + b).Prime := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun a ha b hb hab => (hN (a + b) hab).mp ⟨a, ha, b, hb, rfl⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite support for the actual positive-integer giant extension -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrimeRange_prime (G : ℝ) :
    ∀ p ∈ smoothGiantPrimeRange G, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2

/-- No positive integer outside this range contributes to the extension.
The endpoints are retained in the finite set. -/
theorem smoothGiant_weight_zero_outside (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : 0 < p)
    (hpI : p ∉ smoothGiantIntegerRange G) : φ (Real.log p - G) = 0 := by
  have hceil : ⌈Real.exp (G + 1)⌉₊ < p := by
    have hn : ¬(1 ≤ p ∧ p ≤ ⌈Real.exp (G + 1)⌉₊) := by
      simpa only [smoothGiantIntegerRange, Finset.mem_Icc] using hpI
    omega
  have hexp : Real.exp (G + 1) < (p : ℝ) :=
    (Nat.le_ceil (Real.exp (G + 1))).trans_lt (by exact_mod_cast hceil)
  have hlog : G + 1 < Real.log p := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hexp
  exact hout _ (le_trans (by linarith) (le_abs_self _))

/-- The smooth normalizer has the exact finite support stipulated in (7.3). -/
theorem smoothGiant_prime_support (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : p.Prime)
    (hφp : φ (Real.log p - G) ≠ 0) : p ∈ smoothGiantPrimeRange G := by
  apply Finset.mem_filter.mpr
  refine ⟨?_, hp⟩
  by_contra hn
  exact hφp (smoothGiant_weight_zero_outside φ G hout p hp.pos hn)

/-- A lower bound on the bump in a retained central prime interval gives
an actual lower bound for its normalizer. -/
theorem smoothGiantMass_lower (P S : Finset ℕ) (hSP : S ⊆ P)
    (φ : ℝ → ℝ) (G a : ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (ha : ∀ p ∈ S, a ≤ φ (Real.log p - G)) :
    a * (∑ p ∈ S, (p : ℝ)⁻¹) ≤ smoothGiantMass P φ G := by
  calc
    _ = ∑ p ∈ S, a / (p : ℝ) := by simp only [Finset.mul_sum, div_eq_mul_inv]
    _ ≤ ∑ p ∈ S, φ (Real.log p - G) / (p : ℝ) :=
      Finset.sum_le_sum fun p hp => div_le_div_of_nonneg_right (ha p hp) (Nat.cast_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSP
      (fun p _ _ => div_nonneg (hφ _) (Nat.cast_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantAmbientPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full smooth giant law inside an ambient prime set -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantMass_ambient (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hsub : smoothGiantPrimeRange G ⊆ P) :
    smoothGiantMass P φ G = smoothGiantMass (smoothGiantPrimeRange G) φ G := by
  symm
  apply Finset.sum_subset hsub
  intro p hp hn
  have hz : φ (Real.log p - G) = 0 := by
    by_contra hne
    exact hn (smoothGiant_prime_support φ G hout p (hP p hp) hne)
  simp only [hz, zero_div]

theorem smoothGiantPrior_ambient_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : P) (hp : (p : ℕ) ∉ smoothGiantPrimeRange G) :
    smoothGiantPrior P φ G p = 0 := by
  have hz : φ (Real.log (p : ℕ) - G) = 0 := by
    by_contra hne
    exact hp (smoothGiant_prime_support φ G hout p (hP p p.property) hne)
  simp only [smoothGiantPrior, hz, mul_zero, zero_div]

theorem smoothGiantPrior_ambient_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hsub : smoothGiantPrimeRange G ⊆ P) (f : P → ℝ) :
    (∑ p : P, smoothGiantPrior P φ G p * f p) =
      ∑ q : smoothGiantPrimeRange G, smoothGiantPrior (smoothGiantPrimeRange G) φ G q *
        f ⟨q, hsub q.property⟩ := by
  have hm := smoothGiantMass_ambient P hP φ G hout hsub
  let e : smoothGiantPrimeRange G → P := fun q => ⟨q, hsub q.property⟩
  have hprior (q : smoothGiantPrimeRange G) : smoothGiantPrior P φ G (e q) =
      smoothGiantPrior (smoothGiantPrimeRange G) φ G q := by
    simp only [smoothGiantPrior, smoothGiantLogNormalizer, hm, e]
  have hz (p : P) (hp : (p : ℕ) ∉ smoothGiantPrimeRange G) :
      smoothGiantPrior P φ G p * f p = 0 := by
    rw [smoothGiantPrior_ambient_zero P hP φ G hout p hp, zero_mul]
  calc
    _ = ∑ p ∈ (Finset.univ : Finset P).filter (fun p : P => (p : ℕ) ∈ smoothGiantPrimeRange G),
        smoothGiantPrior P φ G p * f p := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : (p : ℕ) ∈ smoothGiantPrimeRange G
      · simp only [hp, ite_true, if_true]
      · simp only [hp, ite_false, if_false, hz p hp]
    _ = ∑ q : smoothGiantPrimeRange G, smoothGiantPrior P φ G (e q) * f (e q) := by
      symm
      apply Finset.sum_bij (fun q _ => e q)
      · intro q _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.property⟩
      · intro q _ r _ hqr
        exact Subtype.ext (congrArg (fun p : P => p.val) hqr)
      · intro p hp
        refine ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, ?_⟩
        rfl
      · intro q _
        rfl
    _ = _ := by simp only [hprior, e]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem complexUnitPhase_norm_le (z : ℂ) : ‖complexUnitPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [complexUnitPhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    rw [div_self (norm_ne_zero_iff.mpr hz)]

theorem complexUnitPhase_mul_conj (z : ℂ) :
    complexUnitPhase z * conj z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    unfold complexUnitPhase
    rw [div_mul_eq_mul_div, Complex.mul_conj']
    field_simp

theorem densityFourierInverse_energy {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, ‖densityFourierInverse g x‖ ^ 2) = ∑ b, ‖g b‖ ^ 2 := by
  rw [← densityFourier_energy g]
  exact (Equiv.neg (ZMod p)).bijective.sum_comp (fun x => ‖densityFourier g x‖ ^ 2)

theorem phaseGiantPhysical_energy {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, ‖phaseGiantPhysical g x‖ ^ 2) ≤ p := by
  rw [phaseGiantPhysical, densityFourierInverse_energy]
  calc
    _ ≤ ∑ _b : ZMod p, (1 : ℝ) := Finset.sum_le_sum fun b _ =>
      by simpa only [one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (complexUnitPhase_norm_le (g b)) 2
    _ = _ := by simp

/-- The unitary bilinear identity, with the inverse sign explicit. -/
theorem densityFourier_pairing {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) :
    (∑ x, f x * densityFourierInverse g x) =
      ∑ b, densityFourier f (-b) * g b := by
  simp only [densityFourierInverse, densityFourier, additiveFourier_apply,
    Finset.mul_sum, mul_neg, neg_neg, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm b x]
  ring

/-- Flattening preserves the exact positive Fourier pairing used in (7.2). -/
theorem phaseGiantPhysical_pairing {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ)
    (hf : ∀ b, densityFourier f (-b) = conj (densityFourier f b)) :
    (∑ x, f x * phaseGiantPhysical (densityFourier f) x) =
      ((∑ b, ‖densityFourier f b‖ : ℝ) : ℂ) := by
  rw [phaseGiantPhysical, densityFourier_pairing, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [hf, mul_comm, complexUnitPhase_mul_conj]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive uniform-support mean of the Fourier-phase giant -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem densityFourierInverse_sum {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, densityFourierInverse g x) = (Real.sqrt (p : ℝ) : ℂ) * g 0 := by
  have hi := additiveFourier_inversion g 0
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one] at hi
  unfold densityFourierInverse densityFourier
  have hn : (∑ x, additiveFourier g (-x)) = ∑ x, additiveFourier g x := by
    simpa only [Equiv.neg_apply] using
      (Equiv.neg (ZMod p)).bijective.sum_comp (additiveFourier g)
  rw [← Finset.mul_sum, hn, ← hi]

theorem phaseGiantPhysical_sum_zero {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : g 0 = 0) : (∑ x, phaseGiantPhysical g x) = 0 := by
  rw [phaseGiantPhysical, densityFourierInverse_sum, hg, complexUnitPhase_zero, mul_zero]

/-- Exact support sum before converting it to a uniform mean. -/
theorem phaseGiantPhysical_support_sum {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x ∈ S, phaseGiantPhysical (normalizedResidueTransform S) x) =
      (Real.sqrt (residueVariance S) : ℂ) *
        ((∑ b, ‖normalizedResidueTransform S b‖ : ℝ) : ℂ) := by
  let T := phaseGiantPhysical (normalizedResidueTransform S)
  have hs : (Real.sqrt (residueVariance S) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (residueVariance_pos S hS hSp)).ne'
  have hp := phaseGiantPhysical_pairing (normalizedResidueIndicator S)
    (normalizedResidueTransform_neg S)
  change (∑ x, normalizedResidueIndicator S x * T x) =
    ((∑ b, ‖normalizedResidueTransform S b‖ : ℝ) : ℂ) at hp
  have hzero : ∑ x, T x = 0 :=
    phaseGiantPhysical_sum_zero _ (normalizedResidueTransform_zero S)
  have he (x : ZMod p) : normalizedResidueIndicator S x * T x =
      ((if x ∈ S then T x else 0) - (residueDensity S : ℂ) * T x) /
        (Real.sqrt (residueVariance S) : ℂ) := by
    unfold normalizedResidueIndicator centeredDensity residueDensity
    split_ifs <;> push_cast <;> ring
  simp_rw [he] at hp
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, mul_zero, sub_zero] at hp
  have hsum : (∑ x : ZMod p, if x ∈ S then T x else 0) = ∑ x ∈ S, T x := by simp
  rw [hsum] at hp
  exact ((div_eq_iff hs).mp hp).trans (mul_comm _ _)

/-- A fixed positive fraction of the Fourier L1 mean survives on the actual
residue support. The relaxed constant one half is sufficient downstream. -/
theorem phaseGiantPhysical_uniform_mean_lower {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hσ : residueDensity S ≤ 2 / 3) :
    (1 / 2 : ℝ) * ((p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖) ≤
      (S.card : ℝ)⁻¹ * ∑ x ∈ S, (phaseGiantPhysical (normalizedResidueTransform S) x).re := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hσpos : 0 < residueDensity S := div_pos hc hp
  have hvar := residueVariance_pos S hS hSp
  have hroot : residueDensity S / 2 ≤ Real.sqrt (residueVariance S) := by
    have hs := Real.sq_sqrt hvar.le
    dsimp only [residueVariance] at hs ⊢
    have hnn := Real.sqrt_nonneg (residueDensity S * (1 - residueDensity S))
    nlinarith
  have hσp : residueDensity S * p = S.card := by
    unfold residueDensity
    exact div_mul_cancel₀ _ hp.ne'
  have hcoeff : (1 / 2 : ℝ) * (p : ℝ)⁻¹ ≤ (S.card : ℝ)⁻¹ * Real.sqrt (residueVariance S) := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hp hc)).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hroot hp.le]
  have he := congrArg Complex.re (phaseGiantPhysical_support_sum S hS hSp)
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at he
  rw [he]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff
    (Finset.sum_nonneg (s := Finset.univ) fun b _ => norm_nonneg (normalizedResidueTransform S b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedNormTriangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite weighted square norm under divisor summation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem weighted_correlation_le_sqrt_energy {ι : Type*} (S : Finset ι)
    (μ : ι → ℝ) (f g : ι → ℂ) (hμ : ∀ s ∈ S, 0 ≤ μ s) :
    ‖∑ s ∈ S, (μ s : ℂ) * (f s * conj (g s))‖ ≤
      Real.sqrt (∑ s ∈ S, μ s * ‖f s‖ ^ 2) *
      Real.sqrt (∑ s ∈ S, μ s * ‖g s‖ ^ 2) := by
  have he (a : ι → ℂ) : (∑ s ∈ S, (Real.sqrt (μ s) * ‖a s‖) ^ 2) =
      ∑ s ∈ S, μ s * ‖a s‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [mul_pow, Real.sq_sqrt (hμ s hs)]
  calc
    _ ≤ ∑ s ∈ S, μ s * (‖f s‖ * ‖g s‖) := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro s hs
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hμ s hs), Complex.norm_conj]
    _ = ∑ s ∈ S, (Real.sqrt (μ s) * ‖f s‖) * (Real.sqrt (μ s) * ‖g s‖) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [mul_mul_mul_comm, ← pow_two, Real.sq_sqrt (hμ s hs)]
    _ ≤ _ := by
      simpa only [he] using Real.sum_mul_le_sqrt_mul_sqrt S
        (fun s => Real.sqrt (μ s) * ‖f s‖) (fun s => Real.sqrt (μ s) * ‖g s‖)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision control for the unbounded physical giant test -/

namespace Ostmann
open scoped Classical BigOperators

/-- The pointwise inverse bound grows with the prime; the empirical error uses
its counting energy instead and loses exactly one factor of the modulus. -/
theorem phaseGiantPhysical_empirical_error {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (g : ZMod p → ℂ) :
    ‖(∑ x ∈ S, (μ x : ℂ) * phaseGiantPhysical g x) -
      (S.card : ℂ)⁻¹ * ∑ x ∈ S, phaseGiantPhysical g x‖ ^ 2 ≤
        (p : ℝ) * ∑ x ∈ S, (μ x - 1 / (S.card : ℝ)) ^ 2 := by
  have henergy : (∑ x ∈ S, ‖phaseGiantPhysical g x‖ ^ 2) ≤ (p : ℝ) :=
    (Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)).trans
      (phaseGiantPhysical_energy g)
  have h := centered_test_bound S μ (phaseGiantPhysical g) p henergy
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, one_div, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- Weighted Cauchy gives the square-root error in Section 7.1 directly from
the collision budget. No pointwise bound on the inverse transform is used. -/
theorem phaseGiant_weighted_empirical_error {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (μ : ∀ i, ZMod (p i) → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (B : ℝ)
    (hbudget : (∑ i, w i * ((p i : ℝ) *
      ∑ x ∈ S i, (μ i x - 1 / ((S i).card : ℝ)) ^ 2)) ≤ B) :
    ‖∑ i, (w i : ℂ) * ((∑ x ∈ S i, (μ i x : ℂ) * phaseGiantPhysical (g i) x) -
      ((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, phaseGiantPhysical (g i) x)‖ ≤
      Real.sqrt (∑ i, w i) * Real.sqrt B := by
  let E := fun i => (∑ x ∈ S i, (μ i x : ℂ) * phaseGiantPhysical (g i) x) -
    ((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, phaseGiantPhysical (g i) x
  have he : (∑ i, w i * ‖E i‖ ^ 2) ≤ B := by
    apply le_trans _ hbudget
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (phaseGiantPhysical_empirical_error (S i) (μ i) (g i)) (hw i)
  have h := weighted_correlation_le_sqrt_energy Finset.univ w (fun _ => 1) E
    (fun i _ => hw i)
  simp only [one_mul, norm_one, one_pow, mul_one] at h
  have hc : ‖∑ i, (w i : ℂ) * E i‖ = ‖∑ i, (w i : ℂ) * star (E i)‖ := by
    calc
      _ = ‖starRingEnd ℂ (∑ i, (w i : ℂ) * E i)‖ := (Complex.norm_conj _).symm
      _ = _ := by simp only [map_sum, map_mul, Complex.conj_ofReal, Complex.star_def]
  change ‖∑ i, (w i : ℂ) * E i‖ ≤ _
  rw [hc]
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _))

/-- The complex collision estimate implies the required lower bound for the
real empirical mean before the soft-cell pigeonhole. -/
theorem phaseGiant_weighted_empirical_mean_lower {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (μ : ∀ i, ZMod (p i) → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (B : ℝ)
    (hbudget : (∑ i, w i * ((p i : ℝ) *
      ∑ x ∈ S i, (μ i x - 1 / ((S i).card : ℝ)) ^ 2)) ≤ B) :
    (∑ i, w i * (((S i).card : ℝ)⁻¹ *
      ∑ x ∈ S i, (phaseGiantPhysical (g i) x).re)) -
        Real.sqrt (∑ i, w i) * Real.sqrt B ≤
      ∑ i, w i * ∑ x ∈ S i, μ i x * (phaseGiantPhysical (g i) x).re := by
  have h := phaseGiant_weighted_empirical_error p S μ g w hw B hbudget
  let e : ℂ := ∑ i, (w i : ℂ) * ((∑ x ∈ S i, (μ i x : ℂ) * phaseGiantPhysical (g i) x) -
    ((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, phaseGiantPhysical (g i) x)
  have he : -e.re ≤ ‖e‖ := by
    simpa only [Complex.neg_re, norm_neg] using Complex.re_le_norm (-e)
  have hr : e.re =
      (∑ i, w i * ∑ x ∈ S i, μ i x * (phaseGiantPhysical (g i) x).re) -
      (∑ i, w i * (((S i).card : ℝ)⁻¹ * ∑ x ∈ S i, (phaseGiantPhysical (g i) x).re)) := by
    dsimp only [e]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.re_sum, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, mul_sub, Finset.sum_sub_distrib]
  change ‖e‖ ≤ _ at h
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MaskedPhaseGiantMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The favorable-prime mask in the initial giant

Nonfavorable primes remain in the prior. Their physical test is exactly zero.
-/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The favorable Fourier L1 mass gives a positive uniform-support mean,
while the other primes make zero contribution. -/
theorem favorablePhase_uniform_mean_lower {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))
    (F : Finset I) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (γ : ℝ)
    (hS : ∀ i ∈ F, (S i).Nonempty) (hSp : ∀ i ∈ F, (S i).card < p i)
    (hσ : ∀ i ∈ F, residueDensity (S i) ≤ 2 / 3)
    (hγ : ∀ i ∈ F, γ ≤ (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖) :
    (γ / 2) * (∑ i ∈ F, w i) ≤
      ∑ i, w i * (((S i).card : ℝ)⁻¹ *
        ∑ x ∈ S i, (phaseGiantPhysical (favorablePhaseTransform p S F i) x).re) := by
  have hi (i : I) : (if i ∈ F then (γ / 2) * w i else 0) ≤
      w i * (((S i).card : ℝ)⁻¹ *
        ∑ x ∈ S i, (phaseGiantPhysical (favorablePhaseTransform p S F i) x).re) := by
    by_cases hmem : i ∈ F
    · simp only [ite_eq_left hmem, favorablePhaseTransform]
      have hu := phaseGiantPhysical_uniform_mean_lower (S i) (hS i hmem) (hSp i hmem) (hσ i hmem)
      have hh : γ / 2 ≤ ((S i).card : ℝ)⁻¹ *
          ∑ x ∈ S i, (phaseGiantPhysical (normalizedResidueTransform (S i)) x).re := by
        linarith [hγ i hmem]
      simpa only [mul_comm (γ / 2)] using mul_le_mul_of_nonneg_left hh (hw i)
    · simp [favorablePhaseTransform, hmem]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simpa only [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum] using hh

/-- The initial empirical mean, with the genuine Fourier phase mask, pays
only the square-root collision loss from Section 7.1. -/
theorem favorablePhase_empirical_mean_lower {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))
    (F : Finset I) (μ : ∀ i, ZMod (p i) → ℝ)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (γ B : ℝ)
    (hS : ∀ i ∈ F, (S i).Nonempty) (hSp : ∀ i ∈ F, (S i).card < p i)
    (hσ : ∀ i ∈ F, residueDensity (S i) ≤ 2 / 3)
    (hγ : ∀ i ∈ F, γ ≤ (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖)
    (hbudget : (∑ i, w i * ((p i : ℝ) *
      ∑ x ∈ S i, (μ i x - 1 / ((S i).card : ℝ)) ^ 2)) ≤ B) :
    (γ / 2) * (∑ i ∈ F, w i) - Real.sqrt (∑ i, w i) * Real.sqrt B ≤
      ∑ i, w i * ∑ x ∈ S i, μ i x *
        (phaseGiantPhysical (favorablePhaseTransform p S F i) x).re := by
  have hu := favorablePhase_uniform_mean_lower p S F w hw γ hS hSp hσ hγ
  have he := phaseGiant_weighted_empirical_mean_lower p S μ
    (favorablePhaseTransform p S F) w hw B hbudget
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandTails
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite tails of the two summands -/

namespace Ostmann

open scoped Classical

theorem summandPrefix_card_split (A : Set ℕ) (lo hi : ℕ) (hle : lo ≤ hi) :
    (summandPrefix A hi).card = (summandPrefix A lo).card + (summandTail A lo hi).card := by
  have hlo : (summandPrefix A hi).filter (fun n => n ≤ lo) = summandPrefix A lo := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix]
    constructor
    · rintro ⟨⟨ha, _⟩, hn⟩; exact ⟨ha, hn⟩
    · rintro ⟨ha, hn⟩; exact ⟨⟨ha, hn.trans hle⟩, hn⟩
  have hhi : (summandPrefix A hi).filter (fun n => ¬ n ≤ lo) = summandTail A lo hi := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix, mem_summandTail]
    constructor
    · rintro ⟨⟨ha, hh⟩, hn⟩; exact ⟨ha, Nat.lt_of_not_ge hn, hh⟩
    · rintro ⟨ha, hn, hh⟩; exact ⟨⟨ha, hh⟩, Nat.not_le_of_lt hn⟩
  have hh := Finset.card_filter_add_card_filter_not (s := summandPrefix A hi) (fun n => n ≤ lo)
  rw [hlo, hhi] at hh
  exact hh.symm

theorem positiveSummandTail_bounds (A : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ positiveSummandTail A lo hi) : (lo : ℤ) < x ∧ x ≤ hi := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail A lo hi n).mp hn
  exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩

theorem negativeSummandTail_bounds (B : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ negativeSummandTail B lo hi) : -(hi : ℤ) ≤ x ∧ x < -(lo : ℤ) := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail B lo hi n).mp hn
  constructor <;> omega

theorem EventuallyPrimeSumset.tail_prime_differences {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N : ℕ, ∀ lo hi : ℕ, N ≤ lo →
      ∀ x ∈ positiveSummandTail A lo hi, ∀ y ∈ negativeSummandTail B lo hi,
        (x - y).natAbs.Prime ∧ (lo : ℤ) < x - y := by
  obtain ⟨N, hN⟩ := h.prime_add
  refine ⟨N, ?_⟩
  intro lo hi hNlo x hx y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
  obtain ⟨hbB, _, _⟩ := (mem_summandTail B lo hi b).mp hb
  have hab : (a : ℤ) - -(b : ℤ) = ((a + b : ℕ) : ℤ) := by push_cast; ring
  rw [hab, Int.natAbs_natCast]
  exact ⟨hN a haA b hbB (by omega), by exact_mod_cast (by omega : lo < a + b)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Residues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complementary residue supports

The elementary reduction in §2 of the manuscript. Only the exclusion of
composite sums is used to separate the tail supports at a prime.
-/

namespace Ostmann

/-- The residue-support reduction requires only unboundedness of a summand. -/
theorem tailResidues_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) :
    (tailResidues A N p).Nonempty := by
  have hnot : ¬ BddAbove A := fun h => hA (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨a, ha, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨(a : ZMod p), a, ⟨ha, hlarge⟩, rfl⟩

theorem negTailResidues_nonempty {B : Set ℕ} (hB : B.Infinite) (N p : ℕ) :
    (negTailResidues B N p).Nonempty := by
  have hnot : ¬ BddAbove B := fun h => hB (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨b, hb, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨-(b : ZMod p), b, ⟨hb, hlarge⟩, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted prime collisions

The elementary weighted pair count used in Lemma 2.5 (collision stability).
The diagonal is paid for by the largest atom; unequal pairs are paid for by
one logarithm of the interval length.
-/

namespace Ostmann

open scoped BigOperators

theorem primeCollisionWeight_self (P : Finset ℕ) (a : ℕ) :
    primeCollisionWeight P a a = ∑ p ∈ P, Real.log (p : ℝ) := by
  simp [primeCollisionWeight, Nat.ModEq.refl]

theorem primeCollisionWeight_symm (P : Finset ℕ) (a b : ℕ) :
    primeCollisionWeight P a b = primeCollisionWeight P b a := by
  unfold primeCollisionWeight
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ => ⟨fun h => h.symm, fun h => h.symm⟩)

theorem primeCollisionWeight_le_log {P : Finset ℕ} {a b X : ℕ}
    (hab : a ≠ b) (ha : a ≤ X) (hb : b ≤ X) (hP : ∀ p ∈ P, p.Prime) :
    primeCollisionWeight P a b ≤ Real.log (X : ℝ) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact sum_log_congruent_primes_le P hab hb hP
  · rw [primeCollisionWeight_symm]
    exact sum_log_congruent_primes_le P hba ha hP

/-- The weighted pair count from an off-diagonal logarithmic budget. -/
theorem weighted_prime_collision_bound_of_budget (P S : Finset ℕ) (μ : ℕ → ℝ) (L m : ℝ)
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, p.Prime) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m)
    (hbudget : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → primeCollisionWeight P a b ≤ L) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      L + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  classical
  let W : ℝ := ∑ p ∈ P, Real.log (p : ℝ)
  have hW : 0 ≤ W := Finset.sum_nonneg (fun p hp => Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))
  have hpair : ∀ a ∈ S, ∀ b ∈ S,
      primeCollisionWeight P a b ≤ L + if a = b then W else 0 := by
    intro a ha b hb
    by_cases hab : a = b
    · subst b
      simp only [primeCollisionWeight_self, ite_true, if_true]
      dsimp [W] at *
      linarith
    · simpa [hab] using hbudget a ha b hb hab
  have hsquares : (∑ a ∈ S, μ a ^ 2) ≤ m := by
    calc
      (∑ a ∈ S, μ a ^ 2) ≤ ∑ a ∈ S, m * μ a := by
        apply Finset.sum_le_sum
        intro a ha
        nlinarith [hμ a ha, hatom a ha]
      _ = m := by rw [← Finset.mul_sum, hmass, mul_one]
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, μ a * μ b * (L + if a = b then W else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hpair a ha b hb) (mul_nonneg (hμ a ha) (hμ b hb))
    _ = L + W * ∑ a ∈ S, μ a ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hconstant : (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * L) = L := by
        calc
          _ = ∑ a ∈ S, μ a * (∑ b ∈ S, μ b) * L := by
            apply Finset.sum_congr rfl
            intro a _
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ = L := by
            rw [hmass]
            simp only [mul_one]
            rw [← Finset.sum_mul, hmass, one_mul]
      rw [hconstant]
      congr 1
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq]
      calc
        (∑ a ∈ S, if a ∈ S then μ a * μ a * W else 0) =
            ∑ a ∈ S, W * μ a ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [ha, ite_true, if_true]
          ring
        _ = W * ∑ a ∈ S, μ a ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ L + W * m := add_le_add_right (mul_le_mul_of_nonneg_left hsquares hW) L
    _ = _ := by dsimp [W]; ring

/-- Weighted larger-sieve pair bound on the interval `[0,X]`. -/
theorem weighted_prime_collision_bound (P S : Finset ℕ) (μ : ℕ → ℝ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≤ X) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) :=
  weighted_prime_collision_bound_of_budget P S μ (Real.log X) m
    (Real.log_nonneg (by exact_mod_cast hX)) hP hμ hmass hatom
    (fun a ha b hb hab => primeCollisionWeight_le_log hab (hS a ha) (hS b hb) hP)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Projection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residue projection of finite probability measures

These identities connect the pair count in `WeightedCollision` with the
collision norm of a projected measure, as used in Lemma 2.5 of the paper.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_fiberMass_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β) (F : β → ℝ)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y * F y = ∑ a ∈ s, μ a * F (f a) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun a => μ a * F (f a))]
  apply Finset.sum_congr rfl
  intro y _
  unfold fiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem sum_fiberMass {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y = ∑ a ∈ s, μ a := by
  simpa only [mul_one] using sum_fiberMass_mul s t μ f (fun _ => 1) hf

theorem sum_fiberMass_sq {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, (fiberMass s μ f y) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if f a = f b then μ a * μ b else 0 := by
  classical
  simp only [pow_two]
  rw [sum_fiberMass_mul s t μ f (fiberMass s μ f) hf]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberMass, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eq_comm]

theorem residueMass_sq (s : Finset ℕ) (μ : ℕ → ℝ) {p : ℕ}
    (hp : 0 < p) :
    ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if a ≡ b [MOD p] then μ a * μ b else 0 :=
  sum_fiberMass_sq s (Finset.range p) μ (fun a => a % p)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt a hp))

/-- Reorder the weighted residue collisions as a sum over integer pairs. -/
theorem weighted_residueMass_sq (P s : Finset ℕ) (μ : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) =
    ∑ a ∈ s, ∑ b ∈ s, μ a * μ b * primeCollisionWeight P a b := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ a ∈ s, ∑ b ∈ s,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [residueMass_sq s μ (hP p hp).pos]
      simp only [Finset.mul_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ p ∈ P,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [primeCollisionWeight, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring

/-- The quantitative weighted collision bound for projected probabilities. -/
theorem residue_collision_bound (P s : Finset ℕ) (μ : ℕ → ℝ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ a ∈ s, a ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  rw [weighted_residueMass_sq P s μ hP]
  exact weighted_prime_collision_bound P s μ X m hX hP hs hμ hmass hatom

/-- Residue labels may be changed (in particular, negated) without changing
the collision norm, provided they identify exactly the congruent pairs. -/
theorem fiberMass_sq_eq_residueMass_sq (s t : Finset ℕ) (μ : ℕ → ℝ)
    (f : ℕ → ℕ) {p : ℕ} (hp : 0 < p)
    (hf : ∀ a ∈ s, f a ∈ t)
    (hcongr : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ a ≡ b [MOD p]) :
    (∑ r ∈ t, (fiberMass s μ f r) ^ 2) =
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 := by
  rw [sum_fiberMass_sq s t μ f hf, residueMass_sq s μ hp]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [hcongr a ha b hb]

/-- The weighted pair bound applies on any chosen residue support, including
the negative residue support of the second summand. -/
theorem fiber_collision_bound (P s : Finset ℕ) (μ : ℕ → ℝ)
    (t : ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ a ∈ s, a ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m)
    (hf : ∀ p ∈ P, ∀ a ∈ s, f p a ∈ t p)
    (hcongr : ∀ p ∈ P, ∀ a ∈ s, ∀ b ∈ s, f p a = f p b ↔ a ≡ b [MOD p]) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ t p, (fiberMass s μ (f p) r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  convert residue_collision_bound P s μ X m hX hP hs hμ hmass hatom using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p hp
  rw [fiberMass_sq_eq_residueMass_sq s (t p) μ (f p) (hP p hp).pos
    (hf p hp) (hcongr p hp)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Stability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite collision-stability inequality

This is the finite quantitative calculation in Lemma 2.5 of the manuscript.
The final theorem takes the exact numerical consequences of Chebyshev's
bound and Mertens' first theorem at the chosen cutoff as explicit hypotheses.
No main theorem of the manuscript is assumed here.
-/

namespace Ostmann

open scoped BigOperators

theorem collisionDefect_nonneg {p : ℕ} (s t : Finset ℕ) (μ ν : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty) (hcard : s.card + t.card ≤ p) :
    0 ≤ collisionDefect p s t μ ν := by
  have hspos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hcard' : (s.card : ℝ) + t.card ≤ p := by exact_mod_cast hcard
  have hgap := four_div_le_inverse_add_inverse hspos htpos hcard'
  have hμ : 0 ≤ ∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hν : 0 ≤ ∑ r ∈ t, (ν r - 1 / (t.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold collisionDefect
  linarith

theorem collisionDefect_eq (p : ℕ) (s t : Finset ℕ) (μ ν : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hμ : ∑ r ∈ s, μ r = 1) (hν : ∑ r ∈ t, ν r = 1) :
    collisionDefect p s t μ ν =
      (∑ r ∈ s, μ r ^ 2) + (∑ r ∈ t, ν r ^ 2) - 4 / (p : ℝ) := by
  unfold collisionDefect
  rw [collision_sub_uniform s μ hs hμ, collision_sub_uniform t ν ht hν]
  ring

/-- The sum of stability defects is the sum of the collision energies minus
the universal baseline `4 ∑ log p / p`. -/
theorem weighted_collisionDefect_eq (P : Finset ℕ) (s t : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hμ : ∀ p ∈ P, ∑ r ∈ s p, μ p r = 1)
    (hν : ∀ p ∈ P, ∑ r ∈ t p, ν p r = 1) :
    (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (s p) (t p) (μ p) (ν p)) =
      (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) +
      (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) -
      4 * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
  calc
    _ = ∑ p ∈ P,
        ((Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) +
        (Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) -
        4 * (Real.log (p : ℝ) / (p : ℝ))) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [collisionDefect_eq p (s p) (t p) (μ p) (ν p)
        (hs p hp) (ht p hp) (hμ p hp) (hν p hp)]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- A finite, explicit form of collision stability. The two energy bounds
come from `residue_collision_bound`; the last two hypotheses are exactly
the prime-sum estimates needed at the cutoff, rather than full asymptotic
theories. Mertens' first theorem (1874) supplies the lower prime sum. -/
theorem collision_stability_of_prime_sums (P : Finset ℕ)
    (s t : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (X Q : ℕ) (m K C : ℝ)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hμ : ∀ p ∈ P, ∑ r ∈ s p, μ p r = 1)
    (hν : ∀ p ∈ P, ∑ r ∈ t p, ν p r = 1)
    (hm : 0 ≤ m)
    (henergyμ : (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ))
    (henergyν : (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ))
    (hchebyshev : (∑ p ∈ P, Real.log (p : ℝ)) ≤ K * Q)
    (hmertens : Real.log (Q : ℝ) - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) :
    (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (s p) (t p) (μ p) (ν p)) ≤
      2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C + 2 * m * K * Q := by
  rw [weighted_collisionDefect_eq P s t μ ν hs ht hμ hν]
  have hweight := mul_le_mul_of_nonneg_left hchebyshev hm
  nlinarith

/-- Apply the stability inequality to two actual finite measures on integers.
The maps `f` and `g` label their residue classes; allowing a relabeling is
needed for the negative second summand. The prime-sum hypotheses are the
finite specializations of the published inputs used here. -/
theorem finite_measure_collision_stability (P A B : Finset ℕ)
    (μ ν : ℕ → ℝ) (s t : ℕ → Finset ℕ) (f g : ℕ → ℕ → ℕ)
    (X Q : ℕ) (m K C : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hA : ∀ a ∈ A, a ≤ X) (hB : ∀ b ∈ B, b ≤ X)
    (hμ : ∀ a ∈ A, 0 ≤ μ a) (hν : ∀ b ∈ B, 0 ≤ ν b)
    (hmassμ : ∑ a ∈ A, μ a = 1) (hmassν : ∑ b ∈ B, ν b = 1)
    (hatomμ : ∀ a ∈ A, μ a ≤ m) (hatomν : ∀ b ∈ B, ν b ≤ m)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hf : ∀ p ∈ P, ∀ a ∈ A, f p a ∈ s p)
    (hg : ∀ p ∈ P, ∀ b ∈ B, g p b ∈ t p)
    (hcongrf : ∀ p ∈ P, ∀ a ∈ A, ∀ b ∈ A, f p a = f p b ↔ a ≡ b [MOD p])
    (hcongrg : ∀ p ∈ P, ∀ a ∈ B, ∀ b ∈ B, g p a = g p b ↔ a ≡ b [MOD p])
    (hm : 0 ≤ m)
    (hchebyshev : (∑ p ∈ P, Real.log (p : ℝ)) ≤ K * Q)
    (hmertens : Real.log (Q : ℝ) - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (s p) (t p) (fiberMass A μ (f p)) (fiberMass B ν (g p))) ≤
      2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C + 2 * m * K * Q := by
  apply collision_stability_of_prime_sums P s t
    (fun p => fiberMass A μ (f p)) (fun p => fiberMass B ν (g p))
    X Q m K C hs ht
  · intro p hp
    rw [sum_fiberMass A (s p) μ (f p) (hf p hp)]
    exact hmassμ
  · intro p hp
    rw [sum_fiberMass B (t p) ν (g p) (hg p hp)]
    exact hmassν
  · exact hm
  · exact fiber_collision_bound P A μ s f X m hX hP hA hμ hmassμ hatomμ hf hcongrf
  · exact fiber_collision_bound P B ν t g X m hX hP hB hν hmassν hatomν hg hcongrg
  · exact hchebyshev
  · exact hmertens

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailStability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision stability on the two summand tails

This specializes the finite collision bound to the complementary supports
forced by an eventual prime decomposition. Prime-sum estimates remain
explicit hypotheses; no statement about the existence of a decomposition
is assumed as an analytic input.
-/

namespace Ostmann

open scoped BigOperators

theorem negativeResidue_eq_iff {p a b : ℕ} (hp : 0 < p) :
    negativeResidue p a = negativeResidue p b ↔ a ≡ b [MOD p] := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  unfold negativeResidue
  rw [(ZMod.val_injective p).eq_iff, neg_inj, ZMod.natCast_eq_natCast_iff]

theorem tailSupport_subset (A : Set ℕ) (N p : ℕ) :
    tailSupport A N p ⊆ Finset.range p := by
  classical
  exact Finset.filter_subset _ _

theorem mod_mem_tailSupport {A : Set ℕ} {N p a : ℕ} (hp : 0 < p)
    (ha : a ∈ A) (hlarge : N + p < a) : a % p ∈ tailSupport A N p := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt a hp), ?_⟩
  have heq : ((a % p : ℕ) : ZMod p) = (a : ZMod p) := by simp
  rw [heq]
  exact ⟨a, ⟨ha, hlarge⟩, rfl⟩

theorem tailSupport_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ)
    (hp : 0 < p) : (tailSupport A N p).Nonempty := by
  obtain ⟨_, a, ⟨ha, hlarge⟩, rfl⟩ := tailResidues_nonempty hA N p
  exact ⟨a % p, mod_mem_tailSupport hp ha hlarge⟩

theorem negativeResidue_mem_complement {A B : Set ℕ} {N p b : ℕ}
    (hp : 0 < p) (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hb : b ∈ B) (hlarge : N + p < b) :
    negativeResidue p b ∈ Finset.range p \ tailSupport A N p := by
  classical
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
  intro hmem
  have ha := (Finset.mem_filter.mp hmem).2
  change ((-(b : ZMod p)).val : ZMod p) ∈ tailResidues A N p at ha
  rw [ZMod.natCast_zmod_val] at ha
  exact Set.disjoint_left.mp hdisjoint ha ⟨b, ⟨hb, hlarge⟩, rfl⟩

theorem tailSupport_complement_nonempty {A B : Set ℕ} (hB : B.Infinite)
    {N p : ℕ} (hp : 0 < p)
    (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (Finset.range p \ tailSupport A N p).Nonempty := by
  obtain ⟨_, b, ⟨hb, hlarge⟩, rfl⟩ := negTailResidues_nonempty hB N p
  exact ⟨negativeResidue p b, negativeResidue_mem_complement hp hdisjoint hb hlarge⟩

theorem tailSupport_card_add_complement (A : Set ℕ) (N p : ℕ) :
    (tailSupport A N p).card + (Finset.range p \ tailSupport A N p).card = p := by
  rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card (tailSupport_subset A N p)]
  exact Finset.card_range p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TailDensityMask
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual residue masks for the positive endpoint tail -/

namespace Ostmann

open scoped Classical

theorem tailDensityMask_card (A : Set ℕ) (N p : ℕ) :
    (tailDensityMask A N p).card = (tailSupport A N p).card := by
  apply Finset.card_image_of_injOn
  intro r hr s hs he
  have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
  have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
  have hmod := (ZMod.natCast_eq_natCast_iff' r s p).mp he
  simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hmod

theorem positiveSummandTail_mem_mask (A : Set ℕ) (N lo hi p : ℕ) (hp : 0 < p)
    (hlo : N + p ≤ lo) {x : ℤ} (hx : x ∈ positiveSummandTail A lo hi) :
    (x : ZMod p) ∈ tailDensityMask A N p := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
  apply Finset.mem_image.mpr
  refine ⟨a % p, mod_mem_tailSupport hp haA (lt_of_le_of_lt hlo halo), ?_⟩
  simp

theorem tailDensityMask_density (A : Set ℕ) (N p : ℕ) (hp : 0 < p)
    (hcard : ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) :
    (tailDensityMask A N p).card / (p : ℝ) ≤ 2 / 3 := by
  rw [tailDensityMask_card]
  apply (div_le_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp)).mpr
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailMaskCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tail projection in the giant collision estimate -/

namespace Ostmann
open scoped Classical BigOperators

private theorem tailSupport_cast_injective (A : Set ℕ) (N p : ℕ) :
    Set.InjOn (fun r : ℕ => (r : ZMod p)) (tailSupport A N p) := by
  intro r hr s hs he
  have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
  have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
  have hmod := (ZMod.natCast_eq_natCast_iff' r s p).mp he
  simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hmod

theorem sum_tailDensityMask (A : Set ℕ) (N p : ℕ) (f : ZMod p → ℝ) :
    (∑ x ∈ tailDensityMask A N p, f x) =
      ∑ r ∈ tailSupport A N p, f (r : ZMod p) := by
  exact Finset.sum_image (tailSupport_cast_injective A N p)

theorem tailDensityMask_collision_le {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N p : ℕ) (hp : 0 < p)
    (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D : Finset ℕ) (μ ν : ℕ → ℝ) :
    (∑ x ∈ tailDensityMask A N p,
      (zmodResidueMass E μ p x - 1 / ((tailDensityMask A N p).card : ℝ)) ^ 2) ≤
      tailCollisionDefect A N p E D μ ν := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  rw [sum_tailDensityMask, tailDensityMask_card]
  have hs : (∑ r ∈ tailSupport A N p,
      (zmodResidueMass E μ p (r : ZMod p) - 1 / ((tailSupport A N p).card : ℝ)) ^ 2) =
      ∑ r ∈ tailSupport A N p,
        (residueMass E μ p r - 1 / ((tailSupport A N p).card : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
    simp only [zmodResidueMass, ZMod.val_natCast, Nat.mod_eq_of_lt hrp]
  rw [hs]
  have hS := tailSupport_nonempty hA N p hp
  have hT := tailSupport_complement_nonempty hB hp hdisjoint
  have hgap := four_div_le_inverse_add_inverse
    (show (0 : ℝ) < (tailSupport A N p).card by exact_mod_cast hS.card_pos)
    (show (0 : ℝ) < (Finset.range p \ tailSupport A N p).card by exact_mod_cast hT.card_pos)
    (show ((tailSupport A N p).card : ℝ) +
      (Finset.range p \ tailSupport A N p).card ≤ p by
      exact_mod_cast (tailSupport_card_add_complement A N p).le)
  have hother : 0 ≤ ∑ r ∈ Finset.range p \ tailSupport A N p,
      (fiberMass D ν (negativeResidue p) r -
        1 / ((Finset.range p \ tailSupport A N p).card : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  dsimp only [tailCollisionDefect, collisionDefect]
  linarith

/-- Projection to the actual finite mask preserves the endpoint average.
No distributional approximation occurs in this identity. -/
theorem tailDensityMask_empirical_mean (A : Set ℕ) (N p : ℕ) (hp : 0 < p)
    (E : Finset ℕ) (μ : ℕ → ℝ) (F : ZMod p → ℝ)
    (hE : ∀ a ∈ E, a ∈ A ∧ N + p < a) :
    (∑ x ∈ tailDensityMask A N p, zmodResidueMass E μ p x * F x) =
      ∑ a ∈ E, μ a * F (a : ZMod p) := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  rw [sum_tailDensityMask]
  have hs : (∑ r ∈ tailSupport A N p, zmodResidueMass E μ p (r : ZMod p) * F r) =
      ∑ r ∈ tailSupport A N p, residueMass E μ p r * F r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
    simp only [zmodResidueMass, ZMod.val_natCast, Nat.mod_eq_of_lt hrp]
  rw [hs]
  have hh := sum_fiberMass_mul E (tailSupport A N p) μ (fun a => a % p)
    (fun r => F (r : ZMod p)) (fun a ha => mod_mem_tailSupport hp (hE a ha).1 (hE a ha).2)
  simpa only [residueMass, ZMod.natCast_mod] using hh

/-- Logarithmic collision stability also controls any smaller prime weights,
including the localized harmonic weights in a giant cell family. -/
theorem tailDensityMask_weighted_collision {A B : Set ℕ}
    (hA : A.Infinite) (hB : B.Infinite) (N : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hdisjoint : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D : Finset ℕ) (μ ν : ℕ → ℝ) (w : P → ℝ) (G C : ℝ)
    (hG : 0 < G)
    (hweight : ∀ p : P, w p * (p : ℝ) ≤ Real.log (p : ℝ) / G)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p E D μ ν) ≤ C) :
    (∑ p : P, w p * ((p : ℝ) * ∑ x ∈ tailDensityMask A N p,
      (zmodResidueMass E μ p x - 1 / ((tailDensityMask A N p).card : ℝ)) ^ 2)) ≤ C / G := by
  have hb : (∑ p : P, Real.log (p : ℝ) * tailCollisionDefect A N p E D μ ν) ≤ C := by
    exact (Finset.sum_coe_sort P (fun p : ℕ =>
      Real.log (p : ℝ) * tailCollisionDefect A N p E D μ ν)).trans_le hbudget
  calc
    _ ≤ ∑ p : P, (Real.log (p : ℝ) / G) * tailCollisionDefect A N p E D μ ν := by
      apply Finset.sum_le_sum
      intro p _
      have he := tailDensityMask_collision_le hA hB N p (hP p p.property).pos
        (hdisjoint p p.property) E D μ ν
      rw [← mul_assoc]
      exact mul_le_mul (hweight p) he
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (div_nonneg (Real.log_natCast_nonneg _) hG.le)
    _ = (∑ p : P, Real.log (p : ℝ) * tailCollisionDefect A N p E D μ ν) / G := by
      simp only [div_mul_eq_mul_div, Finset.sum_div]
    _ ≤ C / G := div_le_div_of_nonneg_right hb hG.le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFormulaRenaming
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the polynomial support bound onto actual finite prime slots -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_prior_reindex {V W A : Type*} [Fintype V] [Fintype W] [Fintype A]
    (e : V ≃ W) (μ : W → A → ℝ) (F : (W → A) → ℂ) :
    (∑ x : V → A, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm)) =
      ∑ x : W → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x := by
  have he := (Equiv.arrowCongr e (Equiv.refl A)).sum_comp
    (fun x : W → A => ((∏ i, μ i (x i) : ℝ) : ℂ) * F x)
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  change ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm) =
    ((∏ i, μ i (x (e.symm i)) : ℝ) : ℂ) * F (x ∘ e.symm)
  congr 2
  simpa only [Equiv.symm_apply_apply] using
    e.prod_comp (fun i => μ i (x (e.symm i)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeCellMassRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform mass comparison for every original short cell -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem double_exp_below_original_mass (b C : ℝ) (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-Real.exp (b * L)) ≤ Real.exp (-C * L) / 4 := by
  filter_upwards [arithmetic_exponent_absorption 0 b 0 (|C| + 4) 1 1 hb hb hb (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  have hlog : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hC := le_abs_self C
  have hL0 : 0 ≤ L := by linarith
  simp only [zero_mul, Real.exp_zero, mul_one, pow_one] at hrate
  have hx : C * L + Real.log 4 ≤ Real.exp (b * L) := by
    nlinarith [abs_nonneg C, mul_le_mul_of_nonneg_right hC hL0]
  calc
    _ ≤ Real.exp (-C * L - Real.log 4) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

theorem PublishedProgressionInput.short_cell_mass_error_rate (P : PublishedProgressionInput) :
    ∀ᶠ L : ℝ in atTop, ∀ (Cell : Type) [Fintype Cell] (Q : ℕ), 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      ∀ u : Cell → ℝ, (∀ c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u c) →
        (∑ c, bulkPrimeErrorFactor P Q (u c)) ≤
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
  filter_upwards [P.bulk_full_progression_budget_rate 1 0, eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro Cell _ Q hQ hlog hcard u hu
  have hcost : (Fintype.card Cell : ℝ) ≤ Real.exp (1 * L ^ 0 +
      1 * L * Real.exp ((14 / 10000 : ℝ) * L)) := by
    apply hcard.trans
    apply Real.exp_le_exp.mpr
    simp only [pow_zero, one_mul]
    nlinarith [Real.exp_nonneg ((14 / 10000 : ℝ) * L)]
  calc
    _ ≤ ∑ _c : Cell, bulkPrimeErrorFactor P Q (Real.exp ((39 / 10000 : ℝ) * L)) :=
      Finset.sum_le_sum fun c _ => bulkPrimeErrorFactor_antitone P hQ (hu c)
    _ = (Fintype.card Cell : ℝ) * bulkPrimeErrorFactor P Q (Real.exp ((39 / 10000 : ℝ) * L)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := hrate Q hQ hlog _ _ le_rfl hcost

theorem PublishedProgressionInput.short_cell_mass_error_relative (P : PublishedProgressionInput)
    (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (Cell : Type) [Fintype Cell] (Q : ℕ), 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      ∀ u : Cell → ℝ, (∀ c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u c) →
        (∑ c, bulkPrimeErrorFactor P Q (u c)) ≤ Real.exp (-C * L) / 4 := by
  filter_upwards [P.short_cell_mass_error_rate,
    double_exp_below_original_mass (125 / 100000) C (by norm_num)] with L hrate hsmall
  intro Cell _ Q hQ hlog hcard u hu
  exact (hrate Cell Q hQ hlog hcard u hu).trans hsmall

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantMassEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth giant normalizer from the published progression estimate -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators

private theorem central_harmonic_interval_lower (G : ℝ) (hG : 2 ≤ G) :
    (2 * G)⁻¹ ≤ ∫ x in Set.Ioc (G - 1 / 2) (G + 1 / 2), (x : ℝ)⁻¹ := by
  have hu : 0 < G - 1 / 2 := by linarith
  have hv : 0 < G + 1 / 2 := by linarith
  rw [harmonic_box_mass_log _ _ hu (by linarith)]
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hv hu)
  have he : 1 - ((G + 1 / 2) / (G - 1 / 2))⁻¹ = (G + 1 / 2)⁻¹ := by
    field_simp
    ring
  rw [he] at hh
  exact (inv_anti₀ hv (by linarith : G + 1 / 2 ≤ 2 * G)).trans hh

/-- A fixed positive part of the bump supplies a genuine lower bound for
its original prime mass; the only analytic input is the published progression
estimate at modulus one. -/
theorem PublishedProgressionInput.smoothGiantMass_lower
    (P : PublishedProgressionInput) (φ : ℝ → ℝ) (G b : ℝ)
    (hG : 2 ≤ G) (hb : 0 < b) (hφ : ∀ x, 0 ≤ φ x)
    (hcentral : ∀ x, |x| ≤ 1 / 2 → b ≤ φ x)
    (herr : bulkPrimeErrorFactor P 2 (G - 1 / 2) ≤ (4 * G)⁻¹) :
    b / (4 * G) ≤ smoothGiantMass (smoothGiantPrimeRange G) φ G := by
  let S := primeLogCellSet 1 0 (G - 1 / 2) (G + 1 / 2)
  have hSP : S ⊆ smoothGiantPrimeRange G := by
    intro p hp
    obtain ⟨hp, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hp.pos, ?_⟩, hp⟩
    have hlog : Real.log p ≤ G + 1 := by linarith
    have hp' : (p : ℝ) ≤ (⌈Real.exp (G + 1)⌉₊ : ℕ) :=
      ((Real.log_le_iff_le_exp (Nat.cast_pos.mpr hp.pos)).mp hlog).trans (Nat.le_ceil _)
    exact_mod_cast hp'
  have hmass := primeLogCell_page_mass_error P (Q := 2) (q := 1) (a := 0)
    (by omega) (by omega) (by omega) (by simp)
    (G - 1 / 2) (G + 1 / 2) (by linarith) (by linarith) (by linarith)
  rw [primeLogCellMeasure_mass, primeGiantMeasure_one_mass P 2 0 _ _ (by linarith)] at hmass
  have hlo : (4 * G)⁻¹ ≤ ∑ p ∈ S, (p : ℝ)⁻¹ := by
    have hi := central_harmonic_interval_lower G hG
    have he := (abs_le.mp (hmass.trans herr)).1
    have hpos : G ≠ 0 := by linarith
    have hid : (2 * G)⁻¹ = 2 * (4 * G)⁻¹ := by field_simp; ring
    rw [hid] at hi
    dsimp only [S]
    linarith
  have hlower := Ostmann.smoothGiantMass_lower (smoothGiantPrimeRange G) S hSP φ G b hφ
    (fun p hp => by
      obtain ⟨_, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hp
      apply hcentral
      rw [abs_le]
      constructor <;> linarith)
  exact (show b / (4 * G) ≤ b * ∑ p ∈ S, (p : ℝ)⁻¹ by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hlo hb.le).trans hlower

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothLogCellProfile
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth partition profile for the original logarithmic cells -/

namespace Ostmann
open Filter
open scoped Classical

theorem logCellCentralLower_pos : 0 < logCellCentralLower := by
  exact lt_min (Real.smoothTransition.pos_of_pos (by norm_num))
    (sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one (by norm_num)))

theorem logCellProfile_central (x : ℝ) (hx : |x| ≤ 1 / 2) :
    logCellCentralLower ≤ logCellProfile x := by
  have hh := abs_le.mp hx
  unfold logCellCentralLower logCellProfile
  by_cases h : 0 ≤ x
  · rw [Real.smoothTransition.one_of_one_le (x := x + 1) (by linarith)]
    have ht := Real.smoothTransition.monotone hh.2
    exact (min_le_right _ _).trans (sub_le_sub_left ht 1)
  · rw [Real.smoothTransition.zero_of_nonpos (le_of_not_ge h), sub_zero]
    exact (min_le_left _ _).trans (Real.smoothTransition.monotone (by linarith))

/-- The two nonzero translates telescope to one on a unit logarithmic cell. -/
theorem logCellProfile_partition (x : ℝ) (hlo : 0 ≤ x) (hhi : x ≤ 1) :
    logCellProfile x + logCellProfile (x - 1) = 1 := by
  unfold logCellProfile
  rw [Real.smoothTransition.one_of_one_le (x := x + 1) (by linarith),
    Real.smoothTransition.zero_of_nonpos (x := x - 1) (by linarith), sub_add_cancel]
  ring

/-- The full integer partition of unity specified for the logarithmic cells.
Only the two translates adjacent to `floor x` can be nonzero. -/
theorem logCellProfile_partition_unity (x : ℝ) :
    (∑' n : ℤ, logCellProfile (x - n)) = 1 := by
  let z := ⌊x⌋
  have hzlo : (z : ℝ) ≤ x := Int.floor_le x
  have hzhi : x < (z : ℝ) + 1 := Int.lt_floor_add_one x
  have hzero (n : ℤ) (hn : n ∉ ({z, z + 1} : Finset ℤ)) :
      logCellProfile (x - n) = 0 := by
    have hne : n ≠ z ∧ n ≠ z + 1 := by simpa only [Finset.mem_insert,
      Finset.mem_singleton, not_or] using hn
    apply logCellProfile_zero_outside
    by_cases hle : n ≤ z
    · have hi : n + 1 ≤ z := by omega
      have hr : (n : ℝ) + 1 ≤ z := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ x - n by linarith).trans (le_abs_self _)
    · have hi : z + 2 ≤ n := by omega
      have hr : (z : ℝ) + 2 ≤ n := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ -(x - n) by linarith).trans (neg_le_abs _)
  rw [tsum_eq_sum hzero, Finset.sum_pair (by omega : z ≠ z + 1)]
  have hp := logCellProfile_partition (x - z) (by linarith) (by linarith)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  rw [Int.cast_add, Int.cast_one]
  congr 2
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SoftPrimeCellSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a smooth prime cell from a positive empirical mean -/

namespace Ostmann
open scoped Classical BigOperators

theorem logCellProfile_zero_off_centers (x : ℝ) (n : ℤ)
    (hn : n ∉ ({⌊x⌋, ⌊x⌋ + 1} : Finset ℤ)) : logCellProfile (x - n) = 0 := by
  have hne : n ≠ ⌊x⌋ ∧ n ≠ ⌊x⌋ + 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn
  apply logCellProfile_zero_outside
  by_cases hle : n ≤ ⌊x⌋
  · have hi : n + 1 ≤ ⌊x⌋ := by omega
    have hr : (n : ℝ) + 1 ≤ (⌊x⌋ : ℤ) := by exact_mod_cast hi
    exact (show (1 : ℝ) ≤ x - n by linarith [Int.floor_le x]).trans (le_abs_self _)
  · have hi : ⌊x⌋ + 2 ≤ n := by omega
    have hr : ((⌊x⌋ : ℤ) : ℝ) + 2 ≤ n := by exact_mod_cast hi
    exact (show (1 : ℝ) ≤ -(x - n) by linarith [Int.lt_floor_add_one x]).trans (neg_le_abs _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_LocalSmoothGiantSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a complete giant cell inside a prescribed finite window

The averaging family may cover boundary primes several times. Its exact
partition weight is retained, so selecting a cell never clips its prime law.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem logCellFamilyWeight_nonneg (C : Finset ℤ) (p : ℕ) :
    0 ≤ logCellFamilyWeight C p :=
  Finset.sum_nonneg fun _ _ => logCellProfile_nonneg _

theorem smoothGiantPrior_real_mean (P : Finset ℕ) (G : ℝ) (f : ℕ → ℝ)
    (hpos : 0 < smoothGiantMass P logCellProfile G) :
    (∑ p : P, smoothGiantPrior P logCellProfile G p * f p) =
      (smoothGiantMass P logCellProfile G)⁻¹ *
        ∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - G) * f p := by
  simp only [smoothGiantPrior, smoothGiantLogNormalizer, Real.exp_neg,
    Real.exp_log hpos, div_eq_mul_inv]
  rw [Finset.mul_sum]
  have he := Finset.sum_coe_sort P (fun p : ℕ =>
    (smoothGiantMass P logCellProfile G)⁻¹ * (p : ℝ)⁻¹ *
      logCellProfile (Real.log p - G) * f p)
  convert he using 1 <;> first | (with_reducible_and_instances rfl) | (apply Finset.sum_congr rfl <;> intro p _ <;> ring)

theorem local_smoothGiantPrior_exists_positive_mean
    (P : Finset ℕ) (C : Finset ℤ) (f : ℕ → ℝ) (δ : ℝ)
    (hmean : δ * (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p) <
      ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p * f p) :
    ∃ n ∈ C, 0 < smoothGiantMass P logCellProfile n ∧
      δ < ∑ p : P, smoothGiantPrior P logCellProfile n p * f p := by
  let mass := fun n : ℤ => ∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - n)
  let total := fun n : ℤ => ∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - n) * f p
  have hm : (∑ n ∈ C, mass n) = ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p := by
    dsimp only [mass, logCellFamilyWeight]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have ht : (∑ n ∈ C, total n) = ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p * f p := by
    dsimp only [total, logCellFamilyWeight]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, Finset.sum_mul]
  obtain ⟨n, hn, hlt⟩ : ∃ n ∈ C, δ * mass n < total n := by
    by_contra! h
    have hh := Finset.sum_le_sum h
    rw [← Finset.mul_sum, hm, ht] at hh
    exact (not_lt_of_ge hh) hmean
  have hnon : 0 ≤ mass n := Finset.sum_nonneg fun p _ =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (logCellProfile_nonneg _)
  have hpos : 0 < mass n := by
    by_contra! hz
    have he : mass n = 0 := le_antisymm hz hnon
    have hpzero : ∀ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - n) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun p _ =>
        mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (logCellProfile_nonneg _))).mp he
    have htzero : total n = 0 := Finset.sum_eq_zero fun p hp => by rw [hpzero p hp, zero_mul]
    rw [he, htzero, mul_zero] at hlt
    exact lt_irrefl _ hlt
  have heq : mass n = smoothGiantMass P logCellProfile n := by
    dsimp only [mass, smoothGiantMass]
    apply Finset.sum_congr rfl
    intro p _
    rw [div_eq_mul_inv, mul_comm]
  rw [heq] at hpos hlt
  refine ⟨n, hn, hpos, ?_⟩
  rw [smoothGiantPrior_real_mean P n f hpos]
  apply (mul_lt_mul_iff_of_pos_left hpos).mp
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  simpa only [mul_comm δ] using hlt

/-- Extra primes of the ambient container have zero weight in the selected
cell. Both its normalizer and its numerator therefore equal the complete
cell expressions. -/
theorem smoothGiant_full_cell_sums (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (G : ℝ) (hsub : smoothGiantPrimeRange G ⊆ P) (f : ℕ → ℝ) :
    smoothGiantMass P logCellProfile G =
      smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
    (∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - G) * f p) =
      ∑ p ∈ smoothGiantPrimeRange G,
        (p : ℝ)⁻¹ * logCellProfile (Real.log p - G) * f p := by
  have hz (p : ℕ) (hp : p ∈ P) (hn : p ∉ smoothGiantPrimeRange G) :
      logCellProfile (Real.log p - G) = 0 := by
    by_contra h
    exact hn (smoothGiant_prime_support logCellProfile G logCellProfile_zero_outside p (hP p hp) h)
  constructor
  · unfold smoothGiantMass
    exact (Finset.sum_subset hsub fun p hp hn => by rw [hz p hp hn, zero_div]).symm
  · exact (Finset.sum_subset hsub fun p hp hn => by rw [hz p hp hn, mul_zero, zero_mul]).symm

/-- A localized positive mean produces the original full smooth harmonic
prior, with no deletion of endpoint primes. -/
theorem complete_smoothGiantPrior_exists_positive_mean
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (C : Finset ℤ)
    (hsub : ∀ n ∈ C, smoothGiantPrimeRange n ⊆ P) (f : ℕ → ℝ) (δ : ℝ)
    (hmean : δ * (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p) <
      ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p * f p) :
    ∃ n ∈ C, 0 < smoothGiantMass (smoothGiantPrimeRange n) logCellProfile n ∧
      δ < ∑ p : smoothGiantPrimeRange n,
        smoothGiantPrior (smoothGiantPrimeRange n) logCellProfile n p * f p := by
  obtain ⟨n, hn, hpos, hlt⟩ := local_smoothGiantPrior_exists_positive_mean P C f δ hmean
  obtain ⟨hm, ht⟩ := smoothGiant_full_cell_sums P hP n (hsub n hn) f
  refine ⟨n, hn, by rwa [← hm], ?_⟩
  rw [smoothGiantPrior_real_mean P n f hpos, hm, ht] at hlt
  rwa [smoothGiantPrior_real_mean _ n f (by rwa [← hm])]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_LogCellFamilyWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete integer cell families around a real prime block -/

namespace Ostmann
open scoped Classical BigOperators

theorem logBlockCenters_bounds (lo hi : ℝ) {n : ℤ} (hn : n ∈ logBlockCenters lo hi) :
    lo - 2 ≤ n ∧ (n : ℝ) ≤ hi + 2 := by
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
  have hl : ((⌊lo⌋ : ℤ) : ℝ) - 1 ≤ n := by exact_mod_cast hnlo
  have hh : (n : ℝ) ≤ ((⌈hi⌉ : ℤ) : ℝ) + 1 := by exact_mod_cast hnhi
  constructor <;> linarith [Int.lt_floor_add_one lo, Int.ceil_lt_add_one hi]

theorem logCellFamilyWeight_le_one (C : Finset ℤ) (p : ℕ) :
    logCellFamilyWeight C p ≤ 1 := by
  let D : Finset ℤ := {⌊Real.log p⌋, ⌊Real.log p⌋ + 1}
  have hs : logCellFamilyWeight C p =
      ∑ n ∈ C ∩ D, logCellProfile (Real.log p - n) := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro n hn hnot
    apply logCellProfile_zero_off_centers
    intro hm
    exact hnot (Finset.mem_inter.mpr ⟨hn, hm⟩)
  rw [hs]
  have hh : (∑ n ∈ C ∩ D, logCellProfile (Real.log p - n)) ≤
      ∑ n ∈ D, logCellProfile (Real.log p - n) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun n _ _ => logCellProfile_nonneg _)
  apply hh.trans_eq
  rw [← logCellProfile_partition_unity (Real.log p)]
  symm
  exact tsum_eq_sum fun n hn => logCellProfile_zero_off_centers (Real.log p) n hn

theorem logBlockCenters_partition (lo hi : ℝ) (p : ℕ)
    (hlo : lo ≤ Real.log p) (hhi : Real.log p ≤ hi) :
    logCellFamilyWeight (logBlockCenters lo hi) p = 1 := by
  rw [logCellFamilyWeight, ← logCellProfile_partition_unity (Real.log p)]
  symm
  apply tsum_eq_sum
  intro n hn
  apply logCellProfile_zero_off_centers
  intro hmem
  apply hn
  apply Finset.mem_Icc.mpr
  have hf : ⌊lo⌋ ≤ ⌊Real.log p⌋ := Int.floor_mono hlo
  have hc : ⌊Real.log p⌋ ≤ ⌈hi⌉ :=
    (Int.floor_le_floor hhi).trans (Int.floor_le_ceil hi)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl <;> omega

theorem logBlockCenters_weight_zero (lo hi : ℝ) (p : ℕ)
    (hout : Real.log p < lo - 3 ∨ hi + 3 < Real.log p) :
    logCellFamilyWeight (logBlockCenters lo hi) p = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hl, hh⟩ := logBlockCenters_bounds lo hi hn
  apply logCellProfile_zero_outside
  rcases hout with hout | hout
  · exact (show 1 ≤ - (Real.log p - n) by linarith).trans (neg_le_abs _)
  · exact (show 1 ≤ Real.log p - n by linarith).trans (le_abs_self _)

/-- One ambient giant container contains every complete cell in the block. -/
theorem logBlockCenters_full_cells (lo hi : ℝ) :
    ∀ n ∈ logBlockCenters lo hi,
      smoothGiantPrimeRange n ⊆ smoothGiantPrimeRange (hi + 2) := by
  intro n hn p hp
  obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1, hpU⟩ := Finset.mem_Icc.mp hpI
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hp1, hpU.trans ?_⟩, hprime⟩
  exact Nat.ceil_mono (Real.exp_le_exp.mpr (by linarith [(logBlockCenters_bounds lo hi hn).2]))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeSumInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators

theorem prime_log_weight_le (Q : ℕ) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤ Real.log 4 * Q := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensPrimeBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact published Mertens input for logarithmic prime bands

F. Mertens, J. reine angew. Math. 78 (1874), 46–62, first theorem,
DOI 10.1515/crll.1874.78.46. Both sides of the bounded-error estimate
are needed to subtract the lower cutoff; the collision argument uses
only its previously recorded lower-bound consequence.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem MertensEstimate.lower {C : ℝ} (h : MertensEstimate C) : MertensLowerBound C := by
  intro Q hQ
  have hh := (abs_le.mp (h Q hQ)).1
  linarith

theorem MertensEstimate.upper {C : ℝ} (h : MertensEstimate C) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) ≤ Real.log Q + C := by
  have hh := (abs_le.mp (h Q hQ)).2
  linarith

theorem floor_exp_log_bounds (T : ℝ) (hT : 1 ≤ T) :
    1 ≤ ⌊Real.exp T⌋₊ ∧ T - Real.log 2 ≤ Real.log (⌊Real.exp T⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp T⌋₊ : ℝ) ≤ T := by
  have he : 2 ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfloor : (1 : ℕ) ≤ ⌊Real.exp T⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (by linarith)
  have hfp : (0 : ℝ) < ⌊Real.exp T⌋₊ := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hfloor)
  have hhalf : Real.exp T / 2 ≤ (⌊Real.exp T⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor (Real.exp T)
    linarith
  have hlo := Real.log_le_log (show 0 < Real.exp T / 2 by positivity) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlo
  have hhi := Real.log_le_log hfp (Nat.floor_le (Real.exp_nonneg T))
  rw [Real.log_exp] at hhi
  exact ⟨hfloor, hlo, hhi⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensShortBlockMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens bounds for the complete giant cell family -/

namespace Ostmann
open scoped Classical BigOperators

theorem mertens_log_block_upper {C : ℝ} (hM : MertensEstimate C)
    (S : Finset ℕ) (s t : ℝ) (hs : 1 ≤ s) (hst : s ≤ t)
    (hS : ∀ p ∈ S, p.Prime ∧ s < Real.log p ∧ Real.log p ≤ t) :
    (∑ p ∈ S, Real.log (p : ℝ) / p) ≤ t - s + Real.log 2 + 2 * C := by
  let D := Nat.primesLE ⌊Real.exp t⌋₊ \ Nat.primesLE ⌊Real.exp s⌋₊
  have hsub : S ⊆ D := by
    intro p hp
    obtain ⟨hprime, hlo, hhi⟩ := hS p hp
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hprime.pos
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Nat.mem_primesLE.mpr
      exact ⟨Nat.le_floor ((Real.log_le_iff_le_exp hp0).mp hhi), hprime⟩
    · intro hh
      have hle : (p : ℝ) ≤ Real.exp s :=
        (Nat.cast_le.mpr (Nat.le_of_mem_primesLE hh)).trans (Nat.floor_le (Real.exp_nonneg _))
      exact (not_le_of_gt hlo) ((Real.log_le_iff_le_exp hp0).mpr hle)
  have hnest : Nat.primesLE ⌊Real.exp s⌋₊ ⊆ Nat.primesLE ⌊Real.exp t⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans
      (Nat.floor_mono (Real.exp_le_exp.mpr hst)), Nat.prime_of_mem_primesLE hp⟩
  have hupper := hM.upper _ (floor_exp_log_bounds t (hs.trans hst)).1
  have hlower := hM.lower _ (floor_exp_log_bounds s hs).1
  calc
    _ ≤ ∑ p ∈ D, Real.log (p : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
    _ = (∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊, Real.log (p : ℝ) / p) -
        ∑ p ∈ Nat.primesLE ⌊Real.exp s⌋₊, Real.log (p : ℝ) / p :=
      Finset.sum_sdiff_eq_sub hnest
    _ ≤ _ := by linarith [(floor_exp_log_bounds t (hs.trans hst)).2.2,
      (floor_exp_log_bounds s hs).2.1]

/-- The total mass of all complete cells near the block is of order its
length divided by its location, including the overlapping boundary cells. -/
theorem logBlock_family_mass_upper {C : ℝ} (hM : MertensEstimate C)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (lo hi : ℝ)
    (hlo : 5 ≤ lo) (hlohi : lo ≤ hi) :
    (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) ≤
      (hi - lo + 8 + Real.log 2 + 2 * C) / (lo - 4) := by
  let Q := P.filter (fun p => logCellFamilyWeight (logBlockCenters lo hi) p ≠ 0)
  have hQ (p : ℕ) (hp : p ∈ Q) :
      p.Prime ∧ lo - 4 < Real.log p ∧ Real.log p ≤ hi + 4 := by
    obtain ⟨hpP, hn⟩ := Finset.mem_filter.mp hp
    have hr : lo - 3 ≤ Real.log p ∧ Real.log p ≤ hi + 3 := by
      constructor
      · by_contra! hh
        exact hn (logBlockCenters_weight_zero lo hi p (Or.inl hh))
      · by_contra! hh
        exact hn (logBlockCenters_weight_zero lo hi p (Or.inr hh))
    exact ⟨hP p hpP, by linarith [hr.1], by linarith [hr.2]⟩
  have he : (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) =
      ∑ p ∈ Q, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hz : logCellFamilyWeight (logBlockCenters lo hi) p = 0 := by
      simpa only [Q, Finset.mem_filter, hp, true_and, not_not] using hn
    rw [hz, mul_zero]
  have hw := mertens_log_block_upper hM Q (lo - 4) (hi + 4)
    (by linarith) (by linarith) hQ
  rw [he]
  apply (le_div_iff₀ (by linarith : 0 < lo - 4)).mpr
  calc
    _ = ∑ p ∈ Q, (lo - 4) * (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p ∈ Q, Real.log (p : ℝ) / p := by
      apply Finset.sum_le_sum
      intro p hp
      have h1 := logCellFamilyWeight_le_one (logBlockCenters lo hi) p
      have h0 := logCellFamilyWeight_nonneg (logBlockCenters lo hi) p
      calc
        _ ≤ (lo - 4) * (p : ℝ)⁻¹ :=
          mul_le_of_le_one_right (mul_nonneg (by linarith) (by positivity)) h1
        _ ≤ Real.log (p : ℝ) / p := by
          simpa only [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right (hQ p hp).2.1.le (by positivity : 0 ≤ (p : ℝ)⁻¹)
    _ ≤ _ := by linarith

/-- Localized harmonic weights fit directly under the logarithmic collision
budget. The zero-weight primes in the large container need no lower bound. -/
theorem logBlock_family_collision_weight (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (lo hi : ℝ) (hlo : 4 < lo) (p : P) :
    ((p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) * (p : ℝ) ≤
      Real.log (p : ℝ) / (lo - 4) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hP p p.property).ne_zero
  rw [mul_right_comm, inv_mul_cancel₀ hp0, one_mul]
  by_cases hz : logCellFamilyWeight (logBlockCenters lo hi) p = 0
  · rw [hz]
    exact div_nonneg (Real.log_natCast_nonneg _) (by linarith)
  · have hl : lo - 3 ≤ Real.log (p : ℝ) := by
      by_contra! hh
      exact hz (logBlockCenters_weight_zero lo hi p (Or.inl hh))
    exact (logCellFamilyWeight_le_one _ _).trans
      ((le_div_iff₀ (by linarith : 0 < lo - 4)).mpr (by linarith))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CompleteTailGiantMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original giant mean from favorable primes and tail collisions

All prime laws in the conclusion are the full smooth harmonic cell laws.
The favorable set is only a mask on the Fourier test, never on the prior.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem tailGiantEndpointMean_eq (A : Set ℕ) (N : ℕ) (F E : Finset ℕ)
    (p : ℕ) [Fact p.Prime] :
    tailGiantEndpointMean A N F E p =
      (E.card : ℝ)⁻¹ * ∑ a ∈ E, (tailGiantPhysical A N F p (a : ZMod p)).re := by
  simp only [tailGiantEndpointMean, dite_eq_left (Fact.out : p.Prime)]

/-- A finite form of (7.2). The remaining numerical premise compares the
favorable harmonic mass with the explicit collision loss and total cell
mass; it does not assume any mean of the giant test. -/
theorem tail_giant_positive_cell {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hdisjoint : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (F E D : Finset ℕ) (hFP : F ⊆ P) (ν : ℕ → ℝ)
    (lo hi γ δ B₀ : ℝ) (hlo : 4 < lo)
    (hsub : ∀ n ∈ logBlockCenters lo hi, smoothGiantPrimeRange n ⊆ P)
    (hFlog : ∀ p ∈ F, lo ≤ Real.log p ∧ Real.log p ≤ hi)
    (hFbal : ∀ p ∈ F, ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3)
    (hFγ : ∀ p (hp : p ∈ F), let _ : Fact p.Prime := ⟨hP p (hFP hp)⟩;
      γ ≤ (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖)
    (hE : ∀ p ∈ P, ∀ a ∈ E, a ∈ A ∧ N + p < a)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p E D
      (fun _ => (E.card : ℝ)⁻¹) ν) ≤ B₀)
    (hgap :
      δ * (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) +
        Real.sqrt (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) *
          Real.sqrt (B₀ / (lo - 4)) < (γ / 2) * ∑ p ∈ F, (p : ℝ)⁻¹) :
    ∃ n ∈ logBlockCenters lo hi,
      0 < smoothGiantMass (smoothGiantPrimeRange n) logCellProfile n ∧
      δ < ∑ p : smoothGiantPrimeRange n,
        smoothGiantPrior (smoothGiantPrimeRange n) logCellProfile n p *
          tailGiantEndpointMean A N F E p := by
  let : ∀ p : P, Fact (p : ℕ).Prime := fun p => ⟨hP p p.property⟩
  let C := logBlockCenters lo hi
  let w : P → ℝ := fun p => (p : ℝ)⁻¹ * logCellFamilyWeight C p
  let Fs : Finset P := Finset.univ.filter fun p => (p : ℕ) ∈ F
  have hw (p : P) : 0 ≤ w p := mul_nonneg (by positivity) (logCellFamilyWeight_nonneg _ _)
  have hFs (p : P) : p ∈ Fs ↔ (p : ℕ) ∈ F := by simp [Fs]
  have hmass : (∑ p : P, w p) = ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p :=
    Finset.sum_coe_sort P (fun p : ℕ => (p : ℝ)⁻¹ * logCellFamilyWeight C p)
  have hFav : (∑ p ∈ Fs, w p) = ∑ p ∈ F, (p : ℝ)⁻¹ := by
    have he : P.filter (fun p => p ∈ F) = F := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hFP h, h⟩⟩
    calc
      (∑ p ∈ Fs, w p) = ∑ p ∈ P, if p ∈ F then (p : ℝ)⁻¹ * logCellFamilyWeight C p else 0 := by
        simp only [Fs, Finset.sum_filter]
        exact Finset.sum_coe_sort P (fun p : ℕ =>
          if p ∈ F then (p : ℝ)⁻¹ * logCellFamilyWeight C p else 0)
      _ = ∑ p ∈ F, (p : ℝ)⁻¹ * logCellFamilyWeight C p := by rw [← Finset.sum_filter, he]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [logBlockCenters_partition lo hi p (hFlog p hp).1 (hFlog p hp).2, mul_one]
  have hb := tailDensityMask_weighted_collision hA hB N P hP hdisjoint E D
    (fun _ => (E.card : ℝ)⁻¹) ν w (lo - 4) B₀ (by linarith)
    (logBlock_family_collision_weight P hP lo hi hlo) hbudget
  have he := favorablePhase_empirical_mean_lower (fun p : P => (p : ℕ))
    (fun p => tailDensityMask A N p) Fs
    (fun p => zmodResidueMass E (fun _ => (E.card : ℝ)⁻¹) p)
    w hw γ (B₀ / (lo - 4))
    (fun p _ => (Finset.image_nonempty.mpr (tailSupport_nonempty hA N p (hP p p.property).pos)))
    (fun p hp => by
      rw [tailDensityMask_card]
      have hh := hFbal p ((hFs p).mp hp)
      have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (hP p p.property).pos
      exact_mod_cast (show ((tailSupport A N p).card : ℝ) < p by linarith))
    (fun p hp => tailDensityMask_density A N p (hP p p.property).pos (hFbal p ((hFs p).mp hp)))
    (fun p hp => hFγ p ((hFs p).mp hp)) hb
  have hphysical (p : P) : favorablePhaseTransform (fun p : P => (p : ℕ))
      (fun p => tailDensityMask A N p) Fs p =
        (if (p : ℕ) ∈ F then normalizedResidueTransform (tailDensityMask A N p) else fun _ => 0) := by
    simp only [favorablePhaseTransform, hFs]
  have heq (p : P) :
      (∑ x ∈ tailDensityMask A N p, zmodResidueMass E (fun _ => (E.card : ℝ)⁻¹) p x *
        (phaseGiantPhysical (favorablePhaseTransform (fun p : P => (p : ℕ))
          (fun p => tailDensityMask A N p) Fs p) x).re) =
      tailGiantEndpointMean A N F E p := by
    rw [hphysical, tailDensityMask_empirical_mean A N p (hP p p.property).pos E
      (fun _ => (E.card : ℝ)⁻¹) _ (hE p p.property)]
    rw [tailGiantEndpointMean_eq, Finset.mul_sum]
    rfl
  simp_rw [heq] at he
  rw [hmass, hFav] at he
  have htotal : (∑ p : P, w p * tailGiantEndpointMean A N F E p) =
      ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p * tailGiantEndpointMean A N F E p :=
    Finset.sum_coe_sort P (fun p : ℕ =>
      (p : ℝ)⁻¹ * logCellFamilyWeight C p * tailGiantEndpointMean A N F E p)
  rw [htotal] at he
  apply complete_smoothGiantPrior_exists_positive_mean P hP C hsub
    (tailGiantEndpointMean A N F E) δ
  dsimp only [C] at he ⊢
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailGiantEndpointStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected giant mean as the actual initial endpoint sum -/

namespace Ostmann
open scoped Classical BigOperators

theorem tailGiantPhysical_eq_primePhysicalTest (A : Set ℕ) (N : ℕ) (F : Finset ℕ)
    (p : ℕ) [Fact p.Prime] :
    tailGiantPhysical A N F p =
      primePhysicalTest (tailDensityMask A N p) true (decide (p ∈ F)) := by
  funext x
  by_cases hp : p ∈ F
  · simp [tailGiantPhysical, primePhysicalTest, hp]
  · simp [tailGiantPhysical, primePhysicalTest, hp]

theorem tailGiantEndpointMean_weighted_sum (A : Set ℕ) (N : ℕ) (F E P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (μ : P → ℝ) :
    let _ : ∀ p : P, Fact (p : ℕ).Prime := fun p => ⟨hP p p.property⟩
    (∑ p : P, μ p * tailGiantEndpointMean A N F E p) =
      (E.card : ℝ)⁻¹ * ∑ a ∈ E,
        (∑ p : P, (μ p : ℂ) * tailGiantPhysical A N F p (a : ZMod (p : ℕ))).re := by
  intro
  simp_rw [tailGiantEndpointMean_eq, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- A selected full-cell mean is a positive sum over the literal integer
endpoint set used in the initial Poisson statistic. -/
theorem tailGiantEndpointMean_endpoint_lower (A : Set ℕ) (N : ℕ) (F E P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (μ : P → ℝ) (δ : ℝ)
    (hE : E.Nonempty) (hmean : δ ≤ ∑ p : P, μ p * tailGiantEndpointMean A N F E p) :
    let _ : ∀ p : P, Fact (p : ℕ).Prime := fun p => ⟨hP p p.property⟩
    ((E.image fun a : ℕ => (a : ℤ)).card : ℝ) * δ ≤
      ∑ a ∈ E.image (fun a : ℕ => (a : ℤ)),
        (∑ p : P, (μ p : ℂ) * primePhysicalTest (tailDensityMask A N p) true
          (decide ((p : ℕ) ∈ F)) (a : ZMod (p : ℕ))).re := by
  intro
  have hc : (0 : ℝ) < E.card := Nat.cast_pos.mpr hE.card_pos
  have hi : Function.Injective (fun a : ℕ => (a : ℤ)) := by
    intro a b h
    change (a : ℤ) = (b : ℤ) at h
    exact_mod_cast h
  rw [Finset.card_image_of_injective _ hi, Finset.sum_image (fun _ _ _ _ h => hi h)]
  have hh := mul_le_mul_of_nonneg_left hmean hc.le
  rw [tailGiantEndpointMean_weighted_sum A N F E P hP μ, ← mul_assoc,
    mul_inv_cancel₀ hc.ne', one_mul] at hh
  simpa only [Int.cast_natCast, tailGiantPhysical_eq_primePhysicalTest] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AmbientTailGiantEndpoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected giant supplies its endpoint mean in the common prime space -/
namespace Ostmann
open scoped Classical BigOperators

theorem ambient_tail_giant_endpoint_lower
    (A : Set ℕ) (N : ℕ) (F E P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (G δ : ℝ) (hsub : smoothGiantPrimeRange G ⊆ P) (hE : E.Nonempty)
    (hmean : δ ≤ ∑ q : smoothGiantPrimeRange G,
      smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G q * tailGiantEndpointMean A N F E q) :
    let _ : ∀ p : P, Fact (p : ℕ).Prime := fun p => ⟨hP p p.property⟩
    ((E.image fun a : ℕ => (a : ℤ)).card : ℝ) * δ ≤
      ∑ a ∈ E.image (fun a : ℕ => (a : ℤ)),
        (∑ p : P, (smoothGiantPrior P logCellProfile G p : ℂ) *
          primePhysicalTest (tailDensityMask A N p) true (decide ((p : ℕ) ∈ F))
            (a : ZMod (p : ℕ))).re := by
  intro
  apply tailGiantEndpointMean_endpoint_lower A N F E P hP
    (smoothGiantPrior P logCellProfile G) δ hE
  have he := smoothGiantPrior_ambient_mean P hP logCellProfile G logCellProfile_zero_outside
    hsub (fun p => tailGiantEndpointMean A N F E p)
  exact hmean.trans_eq he.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RoundedProtectedTarget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The protected target at the rounded integral endpoint -/
namespace Ostmann

theorem movingProtectedTarget_rounded_bounds (k : ℕ) (hk : 2 ≤ k)
    (h lo G Y td totalGap : ℝ) (hh : 1 ≤ h)
    (hYlo : 2 * lo + 2 ^ (k + 1) * (12 * h) ≤ Y)
    (hYhi : Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * h) + 1)
    (hGlo : lo - 2 ≤ G) (hGhi : G ≤ lo - 2 + 12 * h)
    (herror : |totalGap - 2 * td| ≤ h) :
    16 * h ≤ movingProtectedTarget k Y G td totalGap ∧
      movingProtectedTarget k Y G td totalGap ≤ 32 * h := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hp4 : (4 : ℝ) ≤ 2 ^ k := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at hh
    exact hh
  have hph := mul_le_mul_of_nonneg_right hp4 (show 0 ≤ h by linarith)
  obtain ⟨herrlo, herrhi⟩ := abs_le.mp herror
  unfold movingProtectedTarget
  rw [le_div_iff₀ hp, div_le_iff₀ hp]
  rw [pow_succ] at hYlo hYhi
  constructor <;> nlinarith only [hYlo, hYhi, hGlo, hGhi, herrlo, herrhi, hph, hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialProtectedTarget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two cutoff centers fit the protected target -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingInitialGapTotal_linear (k : ℕ) (Bs BD Bz L : ℝ) :
    movingInitialGapTotal k Bs BD Bz L =
      (spectatorBaseGap Bs ((k : ℝ) ^ 4) 1 +
        ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ)) 1) *
          spectatorBulkCount k L := by
  simp only [movingInitialGapTotal, spectatorBaseGap, spectatorStepGap, mul_one,
    add_mul, Finset.sum_mul]

theorem initial_log_center_bounds (m : ℕ) (T : ℝ) (c : ℤ)
    (hc : c ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp T⌉₊) :
    0 ≤ (c : ℝ) ∧ (c : ℝ) ≤ (m : ℝ) * Real.exp T + 1 := by
  have hc0 : 0 ≤ (c : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hc).1
  have hcu : (c : ℝ) ≤ (⌈(m / 2 : ℕ) * Real.exp T⌉₊ : ℕ) := by
    exact_mod_cast (Finset.mem_Icc.mp hc).2
  have hn : ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m 2
  have he := Nat.ceil_lt_add_one (show 0 ≤ ((m / 2 : ℕ) : ℝ) * Real.exp T by positivity)
  exact ⟨hc0, hcu.trans (he.le.trans (by gcongr))⟩

theorem eventual_initial_protected_target (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ cb cd : ℤ,
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      ∀ lo G Y : ℝ,
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      let J := movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L)
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J ∧
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) ∧
      0 ≤ 2 * (cb : ℝ) ∧ 2 * (cb : ℝ) ≤ J / 4 := by
  let z : ℝ := (k : ℝ) ^ 4
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : 1 ≤ z := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz1
  let R := spectatorBaseGap Bs z 1 +
    ∑ i : Fin k, spectatorStepGap BD Bz z ((2 : ℝ) ^ (i : ℕ)) 1
  have hR : 0 ≤ R := by
    dsimp only [R, spectatorBaseGap]
    apply add_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    have hl : 0 ≤ Real.log ((2 : ℝ) ^ (i : ℕ)) :=
      Real.log_nonneg (one_le_pow₀ (by norm_num))
    dsimp only [spectatorStepGap]
    positivity
  let C := max (R * z) (z + 1)
  have hC : 0 ≤ C := (by linarith only [hz] : 0 ≤ z + 1).trans (le_max_right _ _)
  filter_upwards [eventual_protected_target_error C,
    arithmetic_exponent_absorption (6 / 1000) (1 / 100) 0 (z + 1) 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L herror hsmall hL
  intro cb cd hcb hcd lo G Y hYlo hYhi hGlo hGhi J
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hm : (spectatorBulkCount k L : ℝ) ≤ z * L := spectatorBulkCount_upper k L hL0
  obtain ⟨hcb0, hcbU⟩ := initial_log_center_bounds _ _ cb hcb
  obtain ⟨hcd0, hcdU⟩ := initial_log_center_bounds _ _ cd hcd
  have he : Real.exp ((6 / 10000 : ℝ) * L) ≤ Real.exp ((1 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith only [hL0])
  have hE : 1 ≤ Real.exp ((1 / 1000 : ℝ) * L) := Real.one_le_exp (by positivity)
  have hcd1 : (cd : ℝ) ≤ z * L * Real.exp ((1 / 1000 : ℝ) * L) + 1 := by
    have hh := mul_le_mul hm he (Real.exp_nonneg _) (show 0 ≤ z * L by positivity)
    linarith only [hcdU, hh]
  have hcdC : (cd : ℝ) ≤ C * L * Real.exp ((1 / 1000 : ℝ) * L) := by
    have hc := mul_le_mul_of_nonneg_right (le_max_right (R * z) (z + 1))
      (mul_nonneg hL0 (Real.exp_nonneg ((1 / 1000 : ℝ) * L)))
    have hLE : 1 ≤ L * Real.exp ((1 / 1000 : ℝ) * L) := by nlinarith only [hL, hE]
    dsimp only [C]
    nlinarith only [hcd1, hc, hLE]
  have hgap0 : 0 ≤ movingInitialGapTotal k Bs BD Bz L := by
    rw [movingInitialGapTotal_linear]
    exact mul_nonneg hR (Nat.cast_nonneg _)
  have hgapU : movingInitialGapTotal k Bs BD Bz L ≤ C * L := by
    rw [movingInitialGapTotal_linear]
    have hh := mul_le_mul_of_nonneg_right (le_max_left (R * z) (z + 1)) hL0
    have hh' := mul_le_mul_of_nonneg_left hm hR
    change R * (spectatorBulkCount k L : ℝ) ≤ C * L
    dsimp only [C]
    nlinarith only [hh, hh']
  have herr := herror _ cd hgap0 hgapU hcd0 hcdC
  obtain ⟨hJlo, hJhi⟩ := movingProtectedTarget_rounded_bounds k hk _ lo G Y cd _
    (Real.one_le_exp (by positivity)) hYlo hYhi hGlo hGhi herr
  have hcb1 : (cb : ℝ) ≤ z * L * Real.exp ((6 / 1000 : ℝ) * L) + 1 := by
    have hh := mul_le_mul_of_nonneg_right hm (Real.exp_nonneg ((6 / 1000 : ℝ) * L))
    linarith only [hcbU, hh]
  simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hsmall
  have hmul : 0 ≤ (z + 1) * L := mul_nonneg (by positivity) hL0
  have hcb2 : (cb : ℝ) ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hh : 0 ≤ L * Real.exp ((6 / 1000 : ℝ) * L) := by positivity
    nlinarith only [hcb1, hsmall, hmul, hh]
  exact ⟨hJlo, hJhi, by linarith only [hcb0], by
    dsimp only [J]
    linarith only [hJlo, hcb2, Real.exp_nonneg ((1 / 100 : ℝ) * L)]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCountingBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the short initial segment preserves the square-root lower bound -/

namespace Ostmann

open Filter

theorem eventual_tail_counting_budget (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Set ℕ) (lo hi : ℕ), lo ≤ hi → 1 ≤ lo →
      (lo : ℝ) ≤ Real.exp (9 * L / 10) →
      a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix A hi).card →
      (summandPrefix A lo).card ≤ C * Real.sqrt (lo : ℝ) * Real.log (lo : ℝ) ^ 2 →
      (a / 2) * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A lo hi).card := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 20 by norm_num)).const_mul_left
    (2 * C / a)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with L hpoly hL A lo hi hlo h1 hupper hsize hsmall
  have hLp : 0 < L := by linarith
  have hloR : (1 : ℝ) ≤ lo := by exact_mod_cast h1
  have hloPos : (0 : ℝ) < lo := by linarith
  have hlog0 : 0 ≤ Real.log (lo : ℝ) := Real.log_nonneg hloR
  have hlog : Real.log (lo : ℝ) ≤ L := by
    have hh := Real.log_le_log hloPos hupper
    rw [Real.log_exp] at hh
    linarith
  have hsqrt : Real.sqrt (lo : ℝ) ≤ Real.exp (9 * L / 20) := by
    have hh := Real.sqrt_le_sqrt hupper
    have he : Real.exp (9 * L / 10) = (Real.exp (9 * L / 20)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rwa [he, Real.sqrt_sq (Real.exp_nonneg _)] at hh
  have hsmall' : (summandPrefix A lo).card ≤ C * Real.exp (9 * L / 20) * L ^ 2 := by
    apply hsmall.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hC)
      (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _) (by positivity)
  have hpoly' : (2 * C / a) * L ^ 5 ≤ Real.exp (L / 20) := by
    have he : Real.exp ((1 / 20 : ℝ) * L) = Real.exp (L / 20) := by congr 1; ring
    rw [he] at hpoly
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 * C / a) * L ^ 5),
      abs_of_pos (Real.exp_pos _), one_mul] using hpoly
  have hdiscard : C * Real.exp (9 * L / 20) * L ^ 2 ≤ (a / 2) * Real.exp (L / 2) / L ^ 3 := by
    apply (le_div_iff₀ (pow_pos hLp 3)).mpr
    have hh : C * L ^ 5 ≤ (a / 2) * Real.exp (L / 20) := by
      have hm := mul_le_mul_of_nonneg_right hpoly' (show 0 ≤ a / 2 by positivity)
      have hcancel : (2 * C / a) * L ^ 5 * (a / 2) = C * L ^ 5 := by
        calc
          _ = (C * L ^ 5) * (a * a⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ ha.ne', mul_one]
      rw [hcancel] at hm
      linarith only [hm]
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (9 * L / 20))
    have he : Real.exp (9 * L / 20) * Real.exp (L / 20) = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = Real.exp (9 * L / 20) * (C * L ^ 5) := by ring
      _ ≤ Real.exp (9 * L / 20) * ((a / 2) * Real.exp (L / 20)) := hm
      _ = _ := by rw [mul_left_comm, he]
  have hsplit : (summandPrefix A hi).card =
      (summandPrefix A lo).card + (summandTail A lo hi).card := summandPrefix_card_split A lo hi hlo
  have hsplitR : ((summandPrefix A hi).card : ℝ) =
      (summandPrefix A lo).card + (summandTail A lo hi).card := by exact_mod_cast hsplit
  have hh := hsmall'.trans hdiscard
  ring_nf at hh hsize ⊢
  linarith only [hh, hsize, hsplitR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_LargeSummandTails
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large actual tails from the published summand counting bounds -/

namespace Ostmann

open Filter
open scoped Classical

theorem exists_large_summand_tails (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop, ∀ N : ℕ, (N : ℝ) = Real.exp L →
      a * Real.exp (L / 2) / L ^ 3 ≤ (positiveSummandTail A (summandTailCutoff L) N).card ∧
      a * Real.exp (L / 2) / L ^ 3 ≤ (negativeSummandTail B (summandTailCutoff L) N).card ∧
      (∀ x ∈ positiveSummandTail A (summandTailCutoff L) N,
        0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ N) ∧
      (∀ y ∈ negativeSummandTail B (summandTailCutoff L) N,
        -(N : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ 0) ∧
      (∀ x ∈ positiveSummandTail A (summandTailCutoff L) N,
        ∀ y ∈ negativeSummandTail B (summandTailCutoff L) N,
        (x - y).natAbs.Prime ∧ Real.exp (9 * L / 10) < ((x - y).natAbs : ℝ)) := by
  obtain ⟨a, C, ha, hC, N₀, hcounts⟩ := hsize A B hA hB h
  obtain ⟨N₁, hprime⟩ := h.tail_prime_differences
  let K := max N₀ (max N₁ 2)
  refine ⟨a / 2, by positivity, ?_⟩
  filter_upwards [eventual_tail_counting_budget a C ha hC.le,
    eventually_ge_atTop (2 * ((K : ℝ) + 2))] with L hbudget hL N hN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hLpos : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have hKexp : (K : ℝ) ≤ Real.exp (9 * L / 10) := by
    have he := Real.add_one_le_exp (9 * L / 10)
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    linarith
  have hKcut : K ≤ summandTailCutoff L := Nat.le_floor hKexp
  have hcutupper : (summandTailCutoff L : ℝ) ≤ Real.exp (9 * L / 10) :=
    Nat.floor_le (Real.exp_nonneg _)
  have hcutN : summandTailCutoff L ≤ N := by
    have he : Real.exp (9 * L / 10) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
    have hh := hcutupper.trans he
    rw [← hN] at hh
    exact_mod_cast hh
  have hN₀cut : N₀ ≤ summandTailCutoff L := (le_max_left _ _).trans hKcut
  have hN₁cut : N₁ ≤ summandTailCutoff L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hKcut)
  have h2cut : 2 ≤ summandTailCutoff L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hKcut)
  have hcntN := hcounts N (hN₀cut.trans hcutN) (h2cut.trans hcutN)
  have hcntCut := hcounts (summandTailCutoff L) hN₀cut h2cut
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (L / 2) := by
    rw [hN]
    have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hlog : Real.log (N : ℝ) = L := by rw [hN, Real.log_exp]
  have hsa : a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix A N).card := by
    simpa only [hsqrt, hlog] using hcntN.1
  have hsb : a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix B N).card := by
    simpa only [hsqrt, hlog] using hcntN.2.2.1
  have htailA := hbudget A (summandTailCutoff L) N hcutN (by omega) hcutupper hsa hcntCut.2.1
  have htailB := hbudget B (summandTailCutoff L) N hcutN (by omega) hcutupper hsb hcntCut.2.2.2
  refine ⟨by simpa only [positiveSummandTail_card] using htailA,
    by simpa only [negativeSummandTail_card] using htailB, ?_, ?_, ?_⟩
  · intro x hx
    have hb := positiveSummandTail_bounds A _ _ hx
    have hx0 : (0 : ℤ) ≤ x := by omega
    exact ⟨by exact_mod_cast hx0, by exact_mod_cast hb.2⟩
  · intro y hy
    have hb := negativeSummandTail_bounds B _ _ hy
    have hy0 : y ≤ (0 : ℤ) := by omega
    exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hy0⟩
  · intro x hx y hy
    have hp := hprime (summandTailCutoff L) N hN₁cut x hx y hy
    refine ⟨hp.1, ?_⟩
    have hd : 0 ≤ x - y := by omega
    have he : ((x - y).natAbs : ℤ) = x - y := by rw [Int.natCast_natAbs, abs_of_nonneg hd]
    have hn : summandTailCutoff L < (x - y).natAbs := by omega
    exact (Nat.floor_lt (Real.exp_nonneg _)).mp hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCollisionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root prime cutoff and its logarithmic collision budget -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem tailCollisionCutoff_bounds (L : ℝ) (hL : 1 ≤ L)
    (hr : 2 ≤ Real.exp (L / 2) / L ^ 5) :
    1 ≤ tailCollisionCutoff L ∧
    (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) / L ^ 5 ∧
    L / 2 - 5 * Real.log L - Real.log 2 ≤ Real.log (tailCollisionCutoff L : ℝ) := by
  have hLp : 0 < L := by linarith
  have hrp : 0 < Real.exp (L / 2) / L ^ 5 := by positivity
  have hQ : 1 ≤ tailCollisionCutoff L := (Nat.one_le_floor_iff _).mpr (show (1 : ℝ) ≤ _ by linarith)
  have hhalf : (Real.exp (L / 2) / L ^ 5) / 2 ≤ (tailCollisionCutoff L : ℝ) := by
    have hh := Nat.sub_one_lt_floor (Real.exp (L / 2) / L ^ 5)
    change Real.exp (L / 2) / L ^ 5 - 1 < (tailCollisionCutoff L : ℝ) at hh
    linarith
  refine ⟨hQ, Nat.floor_le hrp.le, ?_⟩
  have hh := Real.log_le_log (show 0 < (Real.exp (L / 2) / L ^ 5) / 2 by positivity) hhalf
  rw [Real.log_div (ne_of_gt hrp) (by norm_num),
    Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 5 hLp.ne'),
    Real.log_exp, Real.log_pow] at hh
  exact hh

theorem eventual_tailCollisionCutoff (N : ℕ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 2 ≤ Real.exp (L / 2) / L ^ 5 ∧
      N + tailCollisionCutoff L ≤ summandTailCutoff L := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul_left 2).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (3 * ((N : ℝ) + 3))] with L hb hL
  have hL1 : 1 ≤ L := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hLp : 0 < L := by linarith
  have hpoly : 2 * L ^ 5 ≤ Real.exp (L / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * L ^ 5),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  have hr : 2 ≤ Real.exp (L / 2) / L ^ 5 := (le_div_iff₀ (pow_pos hLp 5)).mpr hpoly
  have hQ := (tailCollisionCutoff_bounds L hL1 hr).2.1
  have hQ' : (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) := hQ.trans
    (div_le_self (Real.exp_nonneg _) (one_le_pow₀ hL1))
  have he : (1 : ℝ) ≤ Real.exp (L / 2) := Real.one_le_exp (by positivity)
  have hN : (N : ℝ) + 3 ≤ Real.exp (2 * L / 5) := by
    have := Real.add_one_le_exp (2 * L / 5)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (L / 2))
  have hexp : Real.exp (L / 2) * Real.exp (2 * L / 5) = Real.exp (9 * L / 10) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at hmul
  have hN0 : 0 ≤ (N : ℝ) + 2 := by positivity
  have hprod := mul_nonneg (sub_nonneg.mpr he) hN0
  have hfloor := Nat.sub_one_lt_floor (Real.exp (9 * L / 10))
  change Real.exp (9 * L / 10) - 1 < (summandTailCutoff L : ℝ) at hfloor
  have hfinal : (N : ℝ) + tailCollisionCutoff L ≤ (summandTailCutoff L : ℝ) := by
    nlinarith only [hmul, hprod, hfloor, hQ']
  exact ⟨hL1, hr, by exact_mod_cast hfinal⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootCollisions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collisions of uniform root populations

The root populations at the end of §3 occupy translated intervals. Their
collision upper bound depends on the diameter and their cardinality.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_uniform_mass (s : Finset ℕ) (hs : s.Nonempty) :
    (∑ _a ∈ s, (1 / (s.card : ℝ))) = 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_one_div_cancel hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_UniformTailStability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic collision defect bound for the actual uniform tails -/

namespace Ostmann

open scoped BigOperators Classical

private theorem uniform_atom_bound (s : Finset ℕ) (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (hsize : a * Real.exp (L / 2) / L ^ 3 ≤ (s.card : ℝ)) :
    s.Nonempty ∧ 1 / (s.card : ℝ) ≤ L ^ 3 / (a * Real.exp (L / 2)) := by
  have hp : 0 < a * Real.exp (L / 2) / L ^ 3 := by positivity
  have hc : (0 : ℝ) < s.card := hp.trans_le hsize
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hc), ?_⟩
  calc
    1 / (s.card : ℝ) ≤ 1 / (a * Real.exp (L / 2) / L ^ 3) := one_div_le_one_div_of_le hp hsize
    _ = _ := by field_simp

theorem uniform_tail_collision_bound {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N lo hi : ℕ) (a L C : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (hr : 2 ≤ Real.exp (L / 2) / L ^ 5) (hhi : (hi : ℝ) = Real.exp L)
    (hlo : N + tailCollisionCutoff L ≤ lo)
    (hdis : ∀ p ∈ Nat.primesLE (tailCollisionCutoff L),
      Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hsizeA : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A lo hi).card)
    (hsizeB : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail B lo hi).card)
    (hM : MertensLowerBound C) :
    (∑ p ∈ Nat.primesLE (tailCollisionCutoff L), Real.log (p : ℝ) *
      tailCollisionDefect A N p (summandTail A lo hi) (summandTail B lo hi)
        (fun _ => 1 / ((summandTail A lo hi).card : ℝ))
        (fun _ => 1 / ((summandTail B lo hi).card : ℝ))) ≤
      20 * Real.log L + 4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a := by
  let Q := tailCollisionCutoff L
  let P := Nat.primesLE Q
  let s := summandTail A lo hi
  let t := summandTail B lo hi
  let m := L ^ 3 / (a * Real.exp (L / 2))
  have hLp : 0 < L := by linarith
  have hs := uniform_atom_bound s a L ha hLp hsizeA
  have ht := uniform_atom_bound t a L ha hLp hsizeB
  have hQ := tailCollisionCutoff_bounds L hL hr
  have hp (p : ℕ) (hp : p ∈ P) : p.Prime := Nat.prime_of_mem_primesLE hp
  have hps (p : ℕ) (hp : p ∈ P) : p ≤ Q := Nat.le_of_mem_primesLE hp
  have hmapA (p : ℕ) (hpP : p ∈ P) (x : ℕ) (hx : x ∈ s) : x % p ∈ tailSupport A N p := by
    obtain ⟨hxA, hxlo, _⟩ := (mem_summandTail A lo hi x).mp hx
    apply mod_mem_tailSupport (hp p hpP).pos hxA
    have := hps p hpP
    omega
  have hmapB (p : ℕ) (hpP : p ∈ P) (x : ℕ) (hx : x ∈ t) :
      negativeResidue p x ∈ Finset.range p \ tailSupport A N p := by
    obtain ⟨hxB, hxlo, _⟩ := (mem_summandTail B lo hi x).mp hx
    apply negativeResidue_mem_complement (hp p hpP).pos (hdis p hpP) hxB
    have := hps p hpP
    omega
  have hX : 1 ≤ hi := by
    have he := Real.one_le_exp hLp.le
    rw [← hhi] at he
    exact_mod_cast he
  have hraw := finite_measure_collision_stability P s t
    (fun _ => 1 / (s.card : ℝ)) (fun _ => 1 / (t.card : ℝ))
    (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
    (fun p x => x % p) negativeResidue hi Q m (Real.log 4) C hX hp
    (fun x hx => ((mem_summandTail A lo hi x).mp hx).2.2)
    (fun x hx => ((mem_summandTail B lo hi x).mp hx).2.2)
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (sum_uniform_mass s hs.1) (sum_uniform_mass t ht.1)
    (fun _ _ => hs.2) (fun _ _ => ht.2)
    (fun p hpP => tailSupport_nonempty hA N p (hp p hpP).pos)
    (fun p hpP => tailSupport_complement_nonempty hB (hp p hpP).pos (hdis p hpP))
    hmapA hmapB (fun _ _ _ _ _ _ => Iff.rfl)
    (fun p hpP _ _ _ _ => negativeResidue_eq_iff (hp p hpP).pos)
    (by positivity) (prime_log_weight_le Q) (hM Q hQ.1)
  change (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p s t
    (fun _ => 1 / (s.card : ℝ)) (fun _ => 1 / (t.card : ℝ))) ≤ _ at hraw
  rw [hhi, Real.log_exp] at hraw
  have hmQ : m * Q ≤ 1 / a := by
    calc
      m * Q ≤ m * (Real.exp (L / 2) / L ^ 5) :=
        mul_le_mul_of_nonneg_left hQ.2.1 (by positivity)
      _ = 1 / (a * L ^ 2) := by dsimp [m]; field_simp
      _ ≤ 1 / a := one_div_le_one_div_of_le ha
        (le_mul_of_one_le_right ha.le (one_le_pow₀ hL))
  have herr := mul_le_mul_of_nonneg_left hmQ (show 0 ≤ 2 * Real.log 4 by positivity)
  dsimp only [Q] at herr
  have herr' : 2 * m * Real.log 4 * (tailCollisionCutoff L : ℝ) ≤ 2 * Real.log 4 / a := by
    first | (convert herr using 1 <;> ring) | exact (le_of_eq (by ring)).trans (herr.trans (le_of_eq (by ring)))
  have hlogQ := hQ.2.2
  dsimp only [P, Q, s, t] at hraw
  linarith only [hraw, herr', hlogQ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailCellWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected small cells lie below the actual collision cutoff -/

namespace Ostmann
open Filter

theorem eventual_tail_cell_window (a C H : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X target : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      Real.exp ((1 / 100 : ℝ) * L) ≤ target →
      target ≤ Real.exp ((11 / 1000 : ℝ) * L) →
      H ≤ target ∧
      target + 64 * tailDefectBudget a C X + 2 ≤ Real.log (tailCollisionCutoff X : ℝ) ∧
      target + 64 * tailDefectBudget a C X + 1 ≤ Real.exp (L / 2) := by
  let D := 256 * C + 256 * Real.log 2 + 128 * Real.log 4 / a + Real.log 2 + 2
  let K := 1290 + |D|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg D]
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht (b : ℝ) (hb : 0 < b) : Tendsto (fun L : ℝ => Real.exp (b * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (4 / 100) 0 K (1 / 2) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_exponent_absorption (11 / 1000) (1 / 2) 0 K 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    (ht (4 / 100) (by norm_num)).eventually (eventually_ge_atTop X₀),
    (ht (1 / 100) (by norm_num)).eventually (eventually_ge_atTop H),
    eventually_ge_atTop (1 : ℝ)] with L hgap hlarge hX0 hH hL
  intro X target hXlo hXhi htlo hthi
  have hcut := hX₀ X (hX0.trans hXlo)
  have hlogX : Real.log X ≤ L := by
    have h := Real.log_le_log (by linarith [hcut.1] : 0 < X) hXhi
    rwa [Real.log_exp] at h
  have htail := (tailCollisionCutoff_bounds X hcut.1 hcut.2.1).2.2
  have hlinear : 1285 * L + D ≤ K * L := by
    have hD := le_abs_self D
    have hDL := mul_le_mul_of_nonneg_left hL (abs_nonneg D)
    dsimp [K]
    nlinarith only [hD, hDL, hL]
  have hprod : Real.exp ((11 / 1000 : ℝ) * L) ≤
      K * L * Real.exp ((11 / 1000 : ℝ) * L) := by
    have hKL : 1 ≤ K * L := hL.trans (le_mul_of_one_le_left (by linarith) hK)
    exact le_mul_of_one_le_left (Real.exp_nonneg _) hKL
  have hbound : target + 64 * tailDefectBudget a C X + 2 +
      5 * Real.log X + Real.log 2 ≤ K * L + K * L * Real.exp ((11 / 1000 : ℝ) * L) := by
    calc
      _ = target + 1285 * Real.log X + D := by dsimp [tailDefectBudget, D]; ring
      _ ≤ Real.exp ((11 / 1000 : ℝ) * L) + 1285 * L + D := by linarith
      _ ≤ _ := by linarith only [hlinear, hprod]
  simp only [pow_one, zero_mul, Real.exp_zero] at hgap hlarge
  refine ⟨hH.trans htlo, ?_, ?_⟩
  · nlinarith only [hbound, hgap, htail, hXlo]
  · have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hcut.1
    have hexp : Real.exp ((1 / 2 : ℝ) * L) = Real.exp (L / 2) := by congr 1; ring
    rw [hexp] at hlarge
    nlinarith only [hbound, hlarge, hlog2, hlogX0]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCellGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected actual cells discharge the diagonal's geometric gap -/

namespace Ostmann
open scoped Classical BigOperators

theorem tailDefectBudget_linear (a C L X : ℝ) (hL : 1 ≤ L)
    (hX : 0 < X) (hXupper : X ≤ Real.exp L) :
    tailDefectBudget a C X ≤ tailCellLinearRate a C * L := by
  have hlog : Real.log X ≤ L := by
    have h := Real.log_le_log hX hXupper
    rwa [Real.log_exp] at h
  have hc := le_abs_self (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a)
  have hcl := mul_le_mul_of_nonneg_left hL
    (abs_nonneg (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a))
  unfold tailDefectBudget tailCellLinearRate
  nlinarith only [hlog, hc, hcl]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailFourierMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One total Fourier-mass function for the actual tail masks -/
namespace Ostmann
open scoped Classical BigOperators

theorem tailFourierMass_eq (A : Set ℕ) (N p : ℕ) [NeZero p] :
    tailFourierMass A N p =
      (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖ := by
  simp only [tailFourierMass, dite_eq_right (NeZero.ne p)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected initial small cells on a common prime space -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialSmallCellList_property (top : ℕ) (centers : List ℕ) (P : ℕ → Prop)
    (htop : P top) (hcenters : ∀ j ∈ centers, P j) :
    ∀ j ∈ initialSmallCellList top centers, P j := by
  intro j hj
  simp only [initialSmallCellList, List.mem_append, List.mem_replicate, List.mem_flatMap] at hj
  rcases hj with ⟨_, rfl⟩ | ⟨w, hw, hjw⟩
  · exact htop
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hjw
    rcases hjw with rfl | rfl <;> exact hcenters _ hw

theorem initial_selected_cells_valid
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets) :
    ∀ j ∈ initialSmallCellList top centers,
      ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j := by
  refine initialSmallCellList_property top centers
    (fun j => ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j) ⟨target, htop⟩ ?_
  induction hcenters with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ⟨w / 4, hj⟩
    · exact ih i hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensHarmonicBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens' second theorem on the iterated-logarithm band

F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine angew.
Math. 78 (1874), 46–62, second theorem. We only require its weaker bounded
error consequence `sum_{p≤Q} 1/p = log log Q + O(1)`. The pinned PNT library
states this specialization as `Mertens.sum_prime_div_eq_log_log`.
-/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem logLogPrimeBand_mem {L : ℝ} {p : ℕ} (hp : p ∈ logLogPrimeBand L) :
    p.Prime ∧ Real.exp ((1 / 20 : ℝ) * L) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ Real.exp ((9 / 10 : ℝ) * L) := by
  obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hp
  have hprime := Nat.prime_of_mem_primesLE hhi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hlo' : ⌊Real.exp (Real.exp ((1 / 20 : ℝ) * L))⌋₊ < p := by
    by_contra hn
    exact hlo (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hn, hprime⟩)
  have hloR : Real.exp (Real.exp ((1 / 20 : ℝ) * L)) < (p : ℝ) :=
    (Nat.floor_lt (Real.exp_nonneg _)).mp hlo'
  have hhiR : (p : ℝ) ≤ Real.exp (Real.exp ((9 / 10 : ℝ) * L)) :=
    (Nat.cast_le.mpr (Nat.le_of_mem_primesLE hhi)).trans (Nat.floor_le (Real.exp_nonneg _))
  exact ⟨hprime, (Real.lt_log_iff_exp_lt hp0).mpr hloR,
    (Real.log_le_iff_le_exp hp0).mpr hhiR⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FavorableBlockEndpoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integral endpoint chosen after the favorable logarithmic block -/
namespace Ostmann
open Filter

/-- Rounding the endpoint up changes its logarithm by at most one. The reserve
in the block leaves every giant-cell prime below the collision cutoff. -/
theorem eventual_favorable_block_endpoint (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ lo : ℝ,
      Real.exp ((5 / 100 : ℝ) * L) ≤ lo → lo ≤ Real.exp ((9 / 10 : ℝ) * L) →
      ∃ Y : ℝ, ∃ hi : ℕ, (hi : ℝ) = Real.exp Y ∧
        2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y ∧
        Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 ∧
        Real.exp ((4 / 100 : ℝ) * L) ≤ Y ∧ Y ≤ Real.exp L ∧
        ⌈Real.exp (lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 3)⌉₊ ≤
          tailCollisionCutoff Y := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [arithmetic_exponent_absorption (9 / 10) 1 0
      (3 + 24 * (2 : ℝ) ^ k) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventual_polynomial_log_budget (8 + |Real.log 2|) 1 (1 / 100) 1 1
      (by positivity) (by norm_num) (by norm_num) (by norm_num),
    ht.eventually (eventually_ge_atTop X₀), eventually_ge_atTop (1 : ℝ)]
    with L hupp hmargin hlarge hL lo hlo hhi
  have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  let t := 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L))
  have hlo0 : 0 < lo := (Real.exp_pos _).trans_le hlo
  have ht0 : 0 < t := by dsimp [t]; positivity
  let hi := ⌈Real.exp t⌉₊
  have hhi0 : (0 : ℝ) < hi := (Real.exp_pos t).trans_le (Nat.le_ceil _)
  have hroundlo : t ≤ Real.log (hi : ℝ) := by
    rw [Real.le_log_iff_exp_le hhi0]
    exact Nat.le_ceil _
  have hroundhi : Real.log (hi : ℝ) ≤ t + 1 := by
    apply (Real.log_le_iff_le_exp hhi0).mpr
    have hc := Nat.ceil_lt_add_one (Real.exp_nonneg t)
    change (hi : ℝ) < Real.exp t + 1 at hc
    have he := Real.add_one_le_exp (1 : ℝ)
    have hte : 1 ≤ Real.exp t := Real.one_le_exp ht0.le
    rw [Real.exp_add]
    nlinarith
  have hYlo : Real.exp ((4 / 100 : ℝ) * L) ≤ Real.log (hi : ℝ) := by
    have hh : Real.exp ((4 / 100 : ℝ) * L) ≤ lo :=
      (Real.exp_le_exp.mpr (by linarith)).trans hlo
    dsimp [t] at hroundlo
    have hp : 0 ≤ (2 : ℝ) ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) := by positivity
    linarith
  have hYhi : Real.log (hi : ℝ) ≤ Real.exp L := by
    have hh : Real.exp ((1 / 100 : ℝ) * L) ≤ Real.exp ((9 / 10 : ℝ) * L) :=
      Real.exp_le_exp.mpr (by linarith)
    have he : 1 ≤ Real.exp ((9 / 10 : ℝ) * L) := Real.one_le_exp (by linarith)
    simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hupp
    dsimp [t] at hroundhi
    rw [pow_succ] at hroundhi
    have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ 24 * (2 : ℝ) ^ k by positivity)
    have hLmul := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ (3 + 24 * (2 : ℝ) ^ k) * Real.exp ((9 / 10 : ℝ) * L) by positivity)
    have hC : 0 ≤ (3 + 24 * (2 : ℝ) ^ k) * L := mul_nonneg (by positivity) (by linarith)
    nlinarith only [hroundhi, hhi, he, hp, hLmul, hupp, hC]
  have hcut := hX₀ _ (hlarge.trans hYlo)
  have hQ := tailCollisionCutoff_bounds _ hcut.1 hcut.2.1
  have hlogY : Real.log (Real.log (hi : ℝ)) ≤ L := by
    apply (Real.log_le_iff_le_exp ((Real.exp_pos _).trans_le hYlo)).mpr hYhi
  have hm := hmargin L (by linarith) (by simp)
  simp only [pow_one, one_mul] at hm
  have hmargin' : 5 * L + Real.log 2 + 3 ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hab := le_abs_self (Real.log 2)
    have ha0 := abs_nonneg (Real.log 2)
    nlinarith
  have hlogcut : lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 3 ≤
      Real.log (tailCollisionCutoff (Real.log (hi : ℝ)) : ℝ) := by
    dsimp [t] at hroundlo
    rw [pow_succ] at hroundlo
    have hp := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    nlinarith only [hQ.2.2, hlogY, hmargin', hroundlo, hp,
      Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  refine ⟨Real.log (hi : ℝ), hi, (Real.exp_log hhi0).symm,
    hroundlo, hroundhi, hYlo, hYhi, ?_⟩
  apply Nat.ceil_le.mpr
  have hQ0 : (0 : ℝ) < tailCollisionCutoff (Real.log (hi : ℝ)) := by exact_mod_cast hQ.1
  simpa only [Real.exp_log hQ0] using Real.exp_le_exp.mpr hlogcut

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialAmbientPrimeRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual collision cutoff contains the complete initial prime space -/
namespace Ostmann
open Filter

theorem eventual_initial_regular_prime_range :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      initialRegularPrimeRange L ⊆ Nat.primesLE (tailCollisionCutoff Y) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [eventual_tail_cell_window 1 0 0,
    ht.eventually (eventually_ge_atTop Y₀), eventually_ge_atTop (0 : ℝ)]
    with L hwindow hlarge hL
  intro Y hYlo hYhi p hp
  have hcut := hY₀ Y (hlarge.trans hYlo)
  have hQ := tailCollisionCutoff_bounds Y hcut.1 hcut.2.1
  have hD : 0 ≤ tailDefectBudget 1 0 Y := by
    dsimp [tailDefectBudget]
    positivity [Real.log_nonneg hcut.1, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num),
      Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hw := (hwindow Y (Real.exp ((11 / 1000 : ℝ) * L)) hYlo hYhi
    (Real.exp_le_exp.mpr (by linarith)) le_rfl).2.1
  have hlog : Real.exp ((11 / 1000 : ℝ) * L) ≤
      Real.log (tailCollisionCutoff Y : ℝ) := by linarith
  have hQ0 : (0 : ℝ) < tailCollisionCutoff Y := by exact_mod_cast hQ.1
  have hbound : Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) ≤
      (tailCollisionCutoff Y : ℝ) := by
    simpa only [Real.exp_log hQ0] using Real.exp_le_exp.mpr hlog
  obtain ⟨hpbound, hpprime⟩ := Nat.mem_primesLE.mp hp
  apply Nat.mem_primesLE.mpr
  refine ⟨?_, hpprime⟩
  exact_mod_cast (show (p : ℝ) ≤ (tailCollisionCutoff Y : ℝ) from
    (Nat.cast_le.mpr hpbound).trans ((Nat.floor_le (Real.exp_nonneg _)).trans hbound))

theorem eventual_initial_giant_prime_range (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ lo Y G : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      smoothGiantPrimeRange G ⊆ Nat.primesLE (tailCollisionCutoff Y) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [eventual_polynomial_log_budget (8 + |Real.log 2|) 1 (1 / 100) 1 1
      (by positivity) (by norm_num) (by norm_num) (by norm_num),
    ht.eventually (eventually_ge_atTop Y₀), eventually_ge_atTop (1 : ℝ)]
    with L hmargin hlarge hL
  intro lo Y G hYlo hYhi hYlower hG p hp
  have hcut := hY₀ Y (hlarge.trans hYlo)
  have hQ := tailCollisionCutoff_bounds Y hcut.1 hcut.2.1
  have hlogY : Real.log Y ≤ L := (Real.log_le_iff_le_exp (by linarith [hcut.1])).mpr hYhi
  have hm := hmargin L (by linarith) (by simp)
  simp only [pow_one, one_mul] at hm
  have hmargin' : 5 * L + Real.log 2 ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hab := le_abs_self (Real.log 2)
    have ha0 := abs_nonneg (Real.log 2)
    nlinarith
  have hpow : (2 : ℝ) ≤ 2 ^ k := by
    calc
      2 = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at hYlower
  have hpw := mul_le_mul_of_nonneg_right hpow
    (Real.exp_nonneg ((1 / 100 : ℝ) * L))
  have hlogcut : G + 1 ≤ Real.log (tailCollisionCutoff Y : ℝ) := by
    nlinarith only [hQ.2.2, hlogY, hmargin', hYlower, hG, hpw,
      Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  have hQ0 : (0 : ℝ) < tailCollisionCutoff Y := by exact_mod_cast hQ.1
  have hceil : ⌈Real.exp (G + 1)⌉₊ ≤ tailCollisionCutoff Y := by
    apply Nat.ceil_le.mpr
    simpa only [Real.exp_log hQ0] using Real.exp_le_exp.mpr hlogcut
  have hp' := Finset.mem_filter.mp hp
  exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hp'.1).2.trans hceil, hp'.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSpectatorSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original spectator coordinates without changing their law -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfAssemble_spectator {P : Type*} (b d r : ℕ)
    (spectator : Fin d → P) (retained : Unit ⊕ (Fin b ⊕ Fin r) → P) (i : Fin d) :
    initialHalfAssemble b d r spectator retained ((i.castAdd r).natAdd b).succ = spectator i := by
  change (Sum.elim spectator retained)
    ((initialSpectatorSlotEquiv b d r).symm (initialSpectatorSlotEquiv b d r (.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem initial_doubled_spectators_injective {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (yl yr : Unit ⊕ (Fin b ⊕ Fin r) → P)
    (h : Function.Injective (Fin.append (initialHalfAssemble b d r sl yl)
      (initialHalfAssemble b d r sr yr))) : Function.Injective (Fin.append sl sr) := by
  obtain ⟨hl, hr, hcross⟩ := Fin.append_injective_iff.mp h
  apply Fin.append_injective_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have he := hl (show initialHalfAssemble b d r sl yl ((i.castAdd r).natAdd b).succ =
        initialHalfAssemble b d r sl yl ((j.castAdd r).natAdd b).succ by
      simpa only [initialHalfAssemble_spectator] using hij)
    have hh : (Sum.inl i : Fin d ⊕ (Unit ⊕ (Fin b ⊕ Fin r))) = Sum.inl j :=
      (initialSpectatorSlotEquiv b d r).injective he
    exact Sum.inl.inj hh
  · intro i j hij
    have he := hr (show initialHalfAssemble b d r sr yr ((i.castAdd r).natAdd b).succ =
        initialHalfAssemble b d r sr yr ((j.castAdd r).natAdd b).succ by
      simpa only [initialHalfAssemble_spectator] using hij)
    have hh : (Sum.inl i : Fin d ⊕ (Unit ⊕ (Fin b ⊕ Fin r))) = Sum.inl j :=
      (initialSpectatorSlotEquiv b d r).injective he
    exact Sum.inl.inj hh
  · intro i j hij
    apply hcross ((i.castAdd r).natAdd b).succ ((j.castAdd r).natAdd b).succ
    simpa only [initialHalfAssemble_spectator] using hij

theorem initial_half_prior_split {P : Type*} [Fintype P] (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (F : (Fin (b + (d + r) + 1) → P) → ℂ) :
    (∑ x, (productPrior (Fin.cons μg (Fin.append μb (Fin.append μd μc))) x : ℂ) * F x) =
      ∑ s : Fin d → P, (productPrior μd s : ℂ) *
        ∑ y : Unit ⊕ (Fin b ⊕ Fin r) → P,
          ((∏ i, (Sum.elim (fun _ => μg) (Sum.elim μb μc)) i (y i) : ℝ) : ℂ) *
            F (initialHalfAssemble b d r s y) := by
  let ν : Fin (b + (d + r) + 1) → P → ℝ :=
    Fin.cons μg (Fin.append μb (Fin.append μd μc))
  have he := finite_prior_reindex (initialSpectatorSlotEquiv b d r) ν F
  change (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) = _
  simp only [finite_univ_canonical] at he ⊢
  rw [← he]
  let e := Equiv.sumArrowEquivProdArrow (Fin d) (Unit ⊕ (Fin b ⊕ Fin r)) P
  have hsplit := e.symm.sum_comp (fun x =>
    ((∏ i, ν (initialSpectatorSlotEquiv b d r i) (x i) : ℝ) : ℂ) *
      F (x ∘ (initialSpectatorSlotEquiv b d r).symm))
  rw [Fintype.sum_prod_type] at hsplit
  simp only [finite_univ_canonical] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have heval : e.symm (s, y) = Sum.elim s y := rfl
  rw [heval]
  rw [← mul_assoc]
  congr 1
  have hprod := Fintype.prod_sum_type (fun i =>
    ν (initialSpectatorSlotEquiv b d r i) ((Sum.elim s y) i))
  simp only [finite_univ_canonical] at hprod
  rw [hprod]
  have hleft : (∏ i : Fin d, ν (initialSpectatorSlotEquiv b d r (.inl i)) (s i)) =
      productPrior μd s := by
    apply Finset.prod_congr rfl
    intro i _
    simp [ν, initialSpectatorSlotEquiv]
  have hright : (∏ i : Unit ⊕ (Fin b ⊕ Fin r),
      ν (initialSpectatorSlotEquiv b d r (.inr i)) (y i)) =
      ∏ i, (Sum.elim (fun _ => μg) (Sum.elim μb μc)) i (y i) := by
    apply Finset.prod_congr rfl
    intro i _
    rcases i with i | (i | i) <;> simp [ν, initialSpectatorSlotEquiv]
  simp only [finite_univ_canonical] at hleft hright
  simp only [Sum.elim_inl, Sum.elim_inr, hleft, hright, Complex.ofReal_mul]

theorem initial_two_half_average {P : Type*} [Fintype P] (n : ℕ)
    (μ : Fin n → P → ℝ) (F : (Fin (n + n) → P) → ℂ) :
    (∑ x, (productPrior (Fin.append μ μ) x : ℂ) * F x) =
      ∑ l : Fin n → P, (productPrior μ l : ℂ) *
        ∑ r : Fin n → P, (productPrior μ r : ℂ) * F (Fin.append l r) := by
  rw [← (initialTwoHalfTupleEquiv P n).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [initialTwoHalfTupleEquiv, Equiv.coe_fn_mk, productPrior, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, Complex.ofReal_mul, mul_assoc]

private theorem initial_complex_average_swap {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℂ) (b : J → ℂ) (F : I → J → ℂ) :
    (∑ i, a i * ∑ j, b j * F i j) = ∑ j, b j * ∑ i, a i * F i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem initial_doubled_prior_split {P : Type*} [Fintype P] (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (F : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ) :
    let ν := Fin.cons μg (Fin.append μb (Fin.append μd μc))
    let νr := Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)
    (∑ x, (productPrior (Fin.append ν ν) x : ℂ) * F x) =
      ∑ sl : Fin d → P, (productPrior μd sl : ℂ) *
        ∑ sr : Fin d → P, (productPrior μd sr : ℂ) *
          ∑ yl : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yl i) : ℝ) : ℂ) *
            ∑ yr : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yr i) : ℝ) : ℂ) *
              F (Fin.append (initialHalfAssemble b d r sl yl) (initialHalfAssemble b d r sr yr)) := by
  intro ν νr
  rw [initial_two_half_average]
  rw [initial_half_prior_split]
  apply Finset.sum_congr rfl
  intro sl _
  congr 1
  calc
    _ = ∑ yl : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yl i) : ℝ) : ℂ) *
        ∑ sr : Fin d → P, (productPrior μd sr : ℂ) *
          ∑ yr : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yr i) : ℝ) : ℂ) *
            F (Fin.append (initialHalfAssemble b d r sl yl) (initialHalfAssemble b d r sr yr)) := by
      apply Finset.sum_congr rfl
      intro yl _
      congr 1
      exact initial_half_prior_split b d r μg μb μd μc _
    _ = _ := initial_complex_average_swap _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSpectatorWitness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing spectators preserves the positive initial amplitude -/
namespace Ostmann
open scoped Classical BigOperators

theorem exists_supported_complex_mean_witness {I : Type*} [Fintype I]
    (μ : I → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1)
    (F : I → ℂ) (β : ℝ) (hmean : β ≤ ‖∑ i, (μ i : ℂ) * F i‖) :
    ∃ i, 0 < μ i ∧ β ≤ ‖F i‖ := by
  by_contra hn
  push Not at hn
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hμ j)).mp
    (show 0 < ∑ i, μ i by rw [hmass]; norm_num)
  have hbound (j : I) : μ j * ‖F j‖ ≤ μ j * β := by
    by_cases hj : 0 < μ j
    · exact mul_le_mul_of_nonneg_left (hn j hj).le (hμ j)
    · have hz : μ j = 0 := le_antisymm (le_of_not_gt hj) (hμ j)
      simp only [hz, zero_mul, le_refl]
  have hstrict : ∑ j, μ j * ‖F j‖ < ∑ j, μ j * β :=
    Finset.sum_lt_sum (fun j _ => hbound j)
      ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hn i hi) hi⟩
  have hnrm : ‖∑ i, (μ i : ℂ) * F i‖ ≤ ∑ i, μ i * ‖F i‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ j)]
  rw [← Finset.sum_mul, hmass, one_mul] at hstrict
  exact (not_lt_of_ge (hmean.trans hnrm)) hstrict

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialFrozenAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Fourier amplitude with both spectator lists fixed -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem regularInitialAmplitude_freeze (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ) :
    let ν := Fin.cons μg (Fin.append μb (Fin.append μd μc))
    regularInitialAmplitude P (Fin.append ν ν) F ψ X V w =
      ∑ sl : Fin d → P, (productPrior μd sl : ℂ) *
        ∑ sr : Fin d → P, (productPrior μd sr : ℂ) *
          initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr := by
  intro ν
  have hh := initial_doubled_prior_split b d r μg μb μd μc
    (fun x => w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0)
  simpa only [regularInitialAmplitude, initialFrozenAmplitude, mul_assoc] using hh

theorem exists_initial_frozen_amplitude (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (hμd : ∀ i p, 0 ≤ μd i p) (hμdmass : ∀ i, ∑ p, μd i p = 1)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ) (β : ℝ)
    (hβ : let ν := Fin.cons μg (Fin.append μb (Fin.append μd μc))
      β ≤ ‖regularInitialAmplitude P (Fin.append ν ν) F ψ X V w‖) :
    ∃ sl sr : Fin d → P,
      (∀ i, μd i (sl i) ≠ 0) ∧ (∀ i, μd i (sr i) ≠ 0) ∧
      β ≤ ‖initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr‖ := by
  dsimp only at hβ
  rw [regularInitialAmplitude_freeze] at hβ
  have hμ := productPrior_nonneg μd hμd
  have hm := productPrior_mass μd hμdmass
  obtain ⟨sl, hsl, hl⟩ := exists_supported_complex_mean_witness (productPrior μd) hμ hm _ β hβ
  obtain ⟨sr, hsr, hr⟩ := exists_supported_complex_mean_witness (productPrior μd) hμ hm _ β hl
  refine ⟨sl, sr, ?_, ?_, hr⟩
  · intro i
    exact (Finset.prod_ne_zero_iff.mp hsl.ne') i (Finset.mem_univ _)
  · intro i
    exact (Finset.prod_ne_zero_iff.mp hsr.ne') i (Finset.mem_univ _)

theorem initialFrozenAmplitude_support (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (sl sr : Fin d → P)
    (hne : initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr ≠ 0) :
    Function.Injective (Fin.append sl sr) := by
  unfold initialFrozenAmplitude at hne
  obtain ⟨yl, _, hyl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hyrsum := right_ne_zero_of_mul hyl
  obtain ⟨yr, _, hyr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hyrsum
  have hkernel := right_ne_zero_of_mul hyr
  have hfull : Function.Injective (Fin.append (initialHalfAssemble b d r sl yl)
      (initialHalfAssemble b d r sr yr)) := by
    by_contra hn
    simp only [hn, ite_false, if_false, mul_zero] at hkernel
    exact hkernel rfl
  exact initial_doubled_spectators_injective b d r sl sr yl yr hfull

theorem exists_distinct_initial_spectators (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (hμd : ∀ i p, 0 ≤ μd i p) (hμdmass : ∀ i, ∑ p, μd i p = 1)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (β : ℝ) (hβpos : 0 < β)
    (hβ : let ν := Fin.cons μg (Fin.append μb (Fin.append μd μc))
      β ≤ ‖regularInitialAmplitude P (Fin.append ν ν) F ψ X V w‖) :
    ∃ sl sr : Fin d → P, Function.Injective (Fin.append sl sr) ∧
      (∀ i, μd i (sl i) ≠ 0) ∧ (∀ i, μd i (sr i) ≠ 0) ∧
      β ≤ ‖initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr‖ := by
  obtain ⟨sl, sr, hsl, hsr, hlower⟩ := exists_initial_frozen_amplitude P b d r
    μg μb μd μc hμd hμdmass F ψ X V w β hβ
  have hne : initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr ≠ 0 :=
    norm_pos_iff.mp (hβpos.trans_le hlower)
  exact ⟨sl, sr, initialFrozenAmplitude_support P b d r μg μb μc F ψ X V w sl sr hne,
    hsl, hsr, hlower⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialTailEndpoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual endpoint tail in the initial Poisson statistic -/
namespace Ostmann
open Filter
open scoped Classical

theorem EventuallyPrimeSumset.initial_tail_endpoint
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite) (N : ℕ) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      let E := positiveSummandTail A (summandTailCutoff Y) hi
      a * Real.sqrt (Real.exp Y) / Y ^ 3 ≤ (E.card : ℝ) ∧ E.Nonempty ∧
      (∀ e ∈ E, (e : ℝ) / Real.exp Y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ e ∈ E, ∀ p : Nat.primesLE (tailCollisionCutoff Y),
        (e : ZMod (p : ℕ)) ∈ tailDensityMask A N p) := by
  obtain ⟨a, ha, htail⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (htail.and (eventual_tailCollisionCutoff N))
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  refine ⟨a, ha, ?_⟩
  filter_upwards [ht.eventually (eventually_ge_atTop Y₀)] with L hL
  intro Y hYlo _hYhi hi hhi E
  obtain ⟨htail, hcut⟩ := hY₀ Y (hL.trans hYlo)
  have ht := htail hi hhi
  have hcount : a * Real.sqrt (Real.exp Y) / Y ^ 3 ≤ (E.card : ℝ) := by
    simpa only [Real.exp_half] using ht.1
  have hpos : 0 < a * Real.sqrt (Real.exp Y) / Y ^ 3 := by
    have hY : 0 < Y := by linarith [hcut.1]
    positivity
  refine ⟨hcount, Finset.card_pos.mp (Nat.cast_pos.mp (hpos.trans_le hcount)), ?_, ?_⟩
  · intro e he
    obtain ⟨he0, hehi⟩ := ht.2.2.1 e he
    rw [hhi] at hehi
    exact ⟨div_nonneg he0 (Real.exp_nonneg _), (div_le_one (Real.exp_pos _)).mpr hehi⟩
  · intro e he p
    have hp := Nat.mem_primesLE.mp p.property
    apply positiveSummandTail_mem_mask A N (summandTailCutoff Y) hi p hp.2.pos _ he
    exact (Nat.add_le_add_left hp.1 N).trans hcut.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantBlockScales
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Specializing the initial giant block to the construction's scales -/

namespace Ostmann
open Filter

theorem eventual_giant_block_scales (a C γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ lo X : ℝ,
      Real.exp ((5 / 100 : ℝ) * L) ≤ lo → lo ≤ Real.exp ((9 / 10 : ℝ) * L) →
      0 < X → X ≤ Real.exp L →
      5 ≤ lo ∧
      8 + Real.log 2 + 2 * C ≤ 10 * Real.exp ((1 / 100 : ℝ) * L) ∧
      lo + 10 * Real.exp ((1 / 100 : ℝ) * L) ≤ 2 * (lo - 4) ∧
      tailDefectBudget a C X ≤ γ ^ 2 * c ^ 2 * (10 * Real.exp ((1 / 100 : ℝ) * L)) / 512 ∧
      (∀ G : ℝ, lo - 2 ≤ G → G ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 2 →
        G ≤ (lo - 2) + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
        2 ≤ G ∧ Real.exp ((39 / 10000 : ℝ) * L) ≤ G - 1 / 2 ∧
        G ≤ Real.exp ((905 / 1000 : ℝ) * L)) := by
  let ε := γ ^ 2 * c ^ 2 * 10 / 512
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hlim : Tendsto (fun L : ℝ => tailCellLinearRate a C *
      (L / Real.exp ((1 / 100 : ℝ) * L))) atTop (nhds 0) := by
    simpa only [pow_one, mul_zero] using
      (isLittleO_pow_exp_pos_mul_atTop 1
        (by norm_num : (0 : ℝ) < 1 / 100)).tendsto_div_nhds_zero.const_mul
          (tailCellLinearRate a C)
  have hratio := hlim.eventually_le_const hε
  have hexp : Tendsto (fun L : ℝ => Real.exp ((1 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [hratio,
    arithmetic_exponent_absorption (1 / 100) (5 / 100) 0 20 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_exponent_absorption (39 / 10000) (5 / 100) 0 4 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_exponent_absorption (9 / 10) (905 / 1000) 0 12 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hexp.eventually (eventually_ge_atTop (max 2 ((8 + Real.log 2 + 2 * C) / 10))),
    eventually_ge_atTop (1 : ℝ)] with L hratio hlow hgap hupp he2 hL
  simp only [pow_one, zero_mul, Real.exp_zero] at hlow hgap hupp hratio
  have hratio' : tailCellLinearRate a C * L ≤ ε * Real.exp ((1 / 100 : ℝ) * L) := by
    rwa [← mul_div_assoc, div_le_iff₀ (Real.exp_pos _)] at hratio
  have he2' : 2 ≤ Real.exp ((1 / 100 : ℝ) * L) := (le_max_left _ _).trans he2
  have heC : (8 + Real.log 2 + 2 * C) / 10 ≤ Real.exp ((1 / 100 : ℝ) * L) :=
    (le_max_right _ _).trans he2
  have hsmallExp : Real.exp ((1 / 100 : ℝ) * L) ≤ Real.exp ((9 / 10 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by nlinarith only [hL])
  have hlow' : 10 * Real.exp ((1 / 100 : ℝ) * L) + 8 ≤
      Real.exp ((5 / 100 : ℝ) * L) := by
    have h := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    nlinarith only [hlow, h, hL, Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  have hgap' : Real.exp ((39 / 10000 : ℝ) * L) + 5 / 2 ≤
      Real.exp ((5 / 100 : ℝ) * L) := by
    have h := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg ((39 / 10000 : ℝ) * L))
    nlinarith only [hgap, h, hL, Real.exp_nonneg ((39 / 10000 : ℝ) * L)]
  have hupp' : Real.exp ((9 / 10 : ℝ) * L) +
      10 * Real.exp ((1 / 100 : ℝ) * L) + 2 ≤ Real.exp ((905 / 1000 : ℝ) * L) := by
    have h := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    nlinarith only [hupp, h, hL, hsmallExp, Real.exp_nonneg ((9 / 10 : ℝ) * L)]
  intro lo X hlo hhi hX hXhi
  refine ⟨by nlinarith only [hlo, hlow', he2'], by linarith only [heC],
    by linarith only [hlo, hlow'], ?_, ?_⟩
  · apply (tailDefectBudget_linear a C L X hL hX hXhi).trans
    calc
      _ ≤ ε * Real.exp ((1 / 100 : ℝ) * L) := hratio'
      _ = _ := by dsimp [ε]; ring
  · intro G hGlo hGhi
    refine ⟨by linarith only [hGhi, he2'], ?_, ?_, by linarith only [hGhi, hhi, hupp']⟩
    · linarith only [hGlo, hlo, hlow', he2']
    · linarith only [hGlo, hlo, hgap']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantNormalizerSharp
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Section 7 bound on the actual giant normalizer -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem PublishedProgressionInput.giant_normalizer_sharp (P : PublishedProgressionInput) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ,
      2 ≤ G → Real.exp ((39 / 10000 : ℝ) * L) ≤ G - 1 / 2 →
      G ≤ Real.exp ((905 / 1000 : ℝ) * L) →
      Real.exp (-(91 / 100 : ℝ) * L) ≤
        smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤
        (91 / 100 : ℝ) * L := by
  have ht : Tendsto (fun L : ℝ => Real.exp ((1 / 200 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [P.short_cell_mass_error_relative (905 / 1000),
    ht.eventually (eventually_ge_atTop (4 / logCellCentralLower)),
    eventually_ge_atTop (4000 : ℝ)] with L herrate hsmall hL
  intro G hG hlo hhi
  have hlog : Real.log (4 * (2 : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 * 2)
    have h2 := Real.add_one_le_exp ((12 / 10000 : ℝ) * L)
    norm_num at h1 ⊢
    nlinarith
  have hcard : (Fintype.card Unit : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) := by
    simpa only [Fintype.card_unique, Nat.cast_one] using
      (Real.one_le_exp (Real.exp_nonneg ((14 / 10000 : ℝ) * L)))
  have herr := herrate Unit 2 (by omega) hlog hcard (fun _ => G - 1 / 2) (fun _ => hlo)
  simp only [Fintype.sum_unique] at herr
  have hinv : Real.exp (-(905 / 1000 : ℝ) * L) ≤ G⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    exact inv_anti₀ (by linarith : 0 < G) hhi
  have herr' : bulkPrimeErrorFactor P 2 (G - 1 / 2) ≤ (4 * G)⁻¹ := by
    apply herr.trans
    calc
      Real.exp (-(905 / 1000 : ℝ) * L) / 4 ≤ G⁻¹ / 4 :=
        div_le_div_of_nonneg_right hinv (by norm_num)
      _ = _ := by ring
  have hm := P.smoothGiantMass_lower logCellProfile G logCellCentralLower hG
    logCellCentralLower_pos logCellProfile_nonneg logCellProfile_central herr'
  have hb : Real.exp (-(1 / 200 : ℝ) * L) ≤ logCellCentralLower / 4 := by
    have hi := inv_anti₀ (div_pos (by norm_num) logCellCentralLower_pos) hsmall
    simpa only [neg_mul, Real.exp_neg, one_div, inv_div, inv_inv] using hi
  have hmass : Real.exp (-(91 / 100 : ℝ) * L) ≤
      smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G := by
    apply le_trans _ hm
    calc
      Real.exp (-(91 / 100 : ℝ) * L) =
          Real.exp (-(1 / 200 : ℝ) * L) * Real.exp (-(905 / 1000 : ℝ) * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (logCellCentralLower / 4) * G⁻¹ :=
        mul_le_mul hb hinv (Real.exp_nonneg _) (div_nonneg logCellCentralLower_pos.le (by norm_num))
      _ = _ := by ring
  refine ⟨hmass, ?_⟩
  have hlogmass := Real.log_le_log (Real.exp_pos _) hmass
  rw [Real.log_exp] at hlogmass
  change -Real.log (smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G) ≤ _
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantMeanGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The numerical margin for the positive giant mean -/

namespace Ostmann
open scoped Classical BigOperators

theorem giant_mean_numeric_gap (M B F h G γ c : ℝ)
    (hM0 : 0 ≤ M) (hB0 : 0 ≤ B) (hh : 0 < h) (hG : 0 < G)
    (hγ : 0 < γ) (hc : 0 < c)
    (hM : M ≤ 2 * h / G) (hB : B ≤ γ ^ 2 * c ^ 2 * h / 512)
    (hF : c * h / (2 * G) ≤ F) :
    (γ * c / 32) * M + Real.sqrt M * Real.sqrt (B / G) < (γ / 2) * F := by
  have hroot0 : 0 ≤ Real.sqrt M * Real.sqrt (B / G) := by positivity
  have hrootSq : (Real.sqrt M * Real.sqrt (B / G)) ^ 2 = M * (B / G) := by
    rw [mul_pow, Real.sq_sqrt hM0, Real.sq_sqrt (div_nonneg hB0 hG.le)]
  have hb' : B / G ≤ (γ ^ 2 * c ^ 2 * h / 512) / G :=
    div_le_div_of_nonneg_right hB hG.le
  have hs : M * (B / G) ≤ (γ * c * h / (16 * G)) ^ 2 := by
    apply (mul_le_mul hM hb' (div_nonneg hB0 hG.le) (by positivity)).trans_eq
    field_simp
    ring
  have hr : Real.sqrt M * Real.sqrt (B / G) ≤ γ * c * h / (16 * G) := by
    have hpos : 0 < γ * c * h / (16 * G) := by positivity
    rw [← hrootSq] at hs
    nlinarith
  have hm : (γ * c / 32) * M ≤ γ * c * h / (16 * G) := by
    apply (mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ γ * c / 32)).trans_eq
    field_simp
    ring
  have hf : γ * c * h / (4 * G) ≤ (γ / 2) * F := by
    apply le_trans _ (mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ γ / 2))
    field_simp
    ring_nf
    exact le_refl _
  have hpos : 0 < γ * c * h / G := by positivity
  have hid : γ * c * h / (4 * G) = 4 * (γ * c * h / (16 * G)) := by ring
  have hid' : γ * c * h / G = 16 * (γ * c * h / (16 * G)) := by ring
  rw [hid] at hf
  rw [hid'] at hpos
  linarith

theorem favorable_block_harmonic_lower (F : Finset ℕ) (G c h : ℝ)
    (hG : 0 < G) (hlog : ∀ p ∈ F, Real.log (p : ℝ) ≤ 2 * G)
    (hmass : c * h ≤ ∑ p ∈ F, Real.log (p : ℝ) / p) :
    c * h / (2 * G) ≤ ∑ p ∈ F, (p : ℝ)⁻¹ := by
  apply (div_le_iff₀ (by positivity : 0 < 2 * G)).mpr
  apply hmass.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_right (hlog p hp) (by positivity : 0 ≤ (p : ℝ)⁻¹)

theorem logBlock_giant_mean_gap {C : ℝ} (hMertens : MertensEstimate C)
    (P F : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (lo h γ c B : ℝ)
    (hlo : 5 ≤ lo) (hh : 0 < h) (hγ : 0 < γ) (hc : 0 < c) (hB0 : 0 ≤ B)
    (hwidth : 8 + Real.log 2 + 2 * C ≤ h)
    (hupper : lo + h ≤ 2 * (lo - 4))
    (hFlog : ∀ p ∈ F, Real.log (p : ℝ) ≤ lo + h)
    (hFmass : c * h ≤ ∑ p ∈ F, Real.log (p : ℝ) / p)
    (hB : B ≤ γ ^ 2 * c ^ 2 * h / 512) :
    (γ * c / 32) *
        (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo (lo + h)) p) +
      Real.sqrt (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo (lo + h)) p) *
        Real.sqrt (B / (lo - 4)) < (γ / 2) * ∑ p ∈ F, (p : ℝ)⁻¹ := by
  apply giant_mean_numeric_gap _ B _ h (lo - 4) γ c
    (Finset.sum_nonneg fun p _ => mul_nonneg (by positivity) (logCellFamilyWeight_nonneg _ _))
    hB0 hh (by linarith) hγ hc
  · apply (logBlock_family_mass_upper hMertens P hP lo (lo + h) hlo (by linarith)).trans
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ lo - 4)
    linarith
  · exact hB
  · exact favorable_block_harmonic_lower F (lo - 4) c h (by linarith)
      (fun p hp => (hFlog p hp).trans hupper) hFmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailGiantBlockSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A full smooth giant selected from a favorable logarithmic prime block -/

namespace Ostmann
open scoped Classical BigOperators

/-- The favorable set affects only the test. The chosen prior contains every
prime of the complete selected cell, and its lower mean is absolute. -/
theorem tail_giant_of_favorable_block {A B : Set ℕ}
    (hA : A.Infinite) (hB : B.Infinite) (N : ℕ)
    (F E D : Finset ℕ) (ν : ℕ → ℝ) (lo h γ c B₀ C : ℝ)
    (hM : MertensEstimate C) (hlo : 5 ≤ lo) (hh : 0 < h)
    (hγ : 0 < γ) (hc : 0 < c) (hB0 : 0 ≤ B₀)
    (hwidth : 8 + Real.log 2 + 2 * C ≤ h)
    (hupper : lo + h ≤ 2 * (lo - 4))
    (hdisjoint : ∀ p ∈ smoothGiantPrimeRange (lo + h + 2),
      Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hF : ∀ p ∈ F, p.Prime ∧ lo ≤ Real.log p ∧ Real.log p ≤ lo + h)
    (hFbal : ∀ p ∈ F, ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3)
    (hFγ : ∀ p (hp : p ∈ F), let _ : Fact p.Prime := ⟨(hF p hp).1⟩;
      γ ≤ (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖)
    (hE : ∀ p ∈ smoothGiantPrimeRange (lo + h + 2), ∀ a ∈ E, a ∈ A ∧ N + p < a)
    (hbudget : (∑ p ∈ smoothGiantPrimeRange (lo + h + 2),
      Real.log (p : ℝ) * tailCollisionDefect A N p E D
        (fun _ => (E.card : ℝ)⁻¹) ν) ≤ B₀)
    (hFmass : c * h ≤ ∑ p ∈ F, Real.log (p : ℝ) / p)
    (hsmall : B₀ ≤ γ ^ 2 * c ^ 2 * h / 512) :
    ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ lo + h + 2 ∧
      0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
      γ * c / 32 < ∑ p : smoothGiantPrimeRange G,
        smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p *
          tailGiantEndpointMean A N F E p := by
  let P := smoothGiantPrimeRange (lo + h + 2)
  have hFP : F ⊆ P := by
    intro p hp
    obtain ⟨hpp, _, hpu⟩ := hF p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hpp.pos, ?_⟩, hpp⟩
    have hlog : Real.log (p : ℝ) ≤ lo + h + 2 + 1 := by linarith
    have he : (p : ℝ) ≤ Real.exp (lo + h + 2 + 1) :=
      (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hpp.pos)).mp hlog
    exact_mod_cast he.trans (Nat.le_ceil _)
  obtain ⟨G, hGC, hmass, hmean⟩ := tail_giant_positive_cell hA hB N P
    (smoothGiantPrimeRange_prime _) hdisjoint F E D hFP ν lo (lo + h) γ (γ * c / 32) B₀
    (by linarith) (logBlockCenters_full_cells lo (lo + h))
    (fun p hp => (hF p hp).2) hFbal hFγ hE hbudget
    (logBlock_giant_mean_gap hM P F (smoothGiantPrimeRange_prime _) lo h γ c B₀
      hlo hh hγ hc hB0 hwidth hupper (fun p hp => (hF p hp).2.2) hFmass hsmall)
  obtain ⟨hGlo, hGhi⟩ := logBlockCenters_bounds lo (lo + h) hGC
  exact ⟨G, hGlo, hGhi, hmass, hmean⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_EventualTailGiant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial giant for the actual large summand tails -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Only the favorable block supply remains as a combinatorial input here.
The endpoint law, collision budget, block margins and normalizer are all
constructed from the actual summands and the cited published inputs. -/
theorem EventuallyPrimeSumset.eventual_giant_from_favorable_blocks
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C γ c : ℝ) (hM : MertensEstimate C) (hγ : 0 < γ) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℝ, Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp X →
      ∀ lo : ℝ, Real.exp ((5 / 100 : ℝ) * L) ≤ lo → lo ≤ Real.exp ((9 / 10 : ℝ) * L) →
      ⌈Real.exp (lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 3)⌉₊ ≤ tailCollisionCutoff X →
      ∀ (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime ∧ lo ≤ Real.log p ∧
        Real.log p ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L)),
      (∀ p ∈ F, ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) →
      (∀ p (hp : p ∈ F), let _ : Fact p.Prime := ⟨(hF p hp).1⟩;
        γ ≤ (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖) →
      c * (10 * Real.exp ((1 / 100 : ℝ) * L)) ≤ ∑ p ∈ F, Real.log (p : ℝ) / p →
      ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ (lo - 2) + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
        Real.exp (-(91 / 100 : ℝ) * L) ≤ smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
        smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100 : ℝ) * L ∧
        γ * c / 32 < ∑ p : smoothGiantPrimeRange G,
          smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p *
            tailGiantEndpointMean A N F (summandTail A (summandTailCutoff X) hi) p := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff N)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventual_giant_block_scales a C γ c hγ hc, P0.giant_normalizer_sharp,
    ht.eventually (eventually_ge_atTop (max X₀ X₁))] with L hscale hnorm hlargeX
  intro X hXlo hXhi hi hhi lo hlo hhiLo hcut F hF hFbal hFγ hFmass
  have hX : 0 < X := (Real.exp_pos _).trans_le hXlo
  have hcuts := hX₁ X ((le_max_right _ _).trans (hlargeX.trans hXlo))
  obtain ⟨hsA, hsB, _, _, _⟩ := hX₀ X ((le_max_left _ _).trans (hlargeX.trans hXlo)) hi hhi
  let width := 10 * Real.exp ((1 / 100 : ℝ) * L)
  let P := smoothGiantPrimeRange (lo + width + 2)
  let E := summandTail A (summandTailCutoff X) hi
  let D := summandTail B (summandTailCutoff X) hi
  have hPprime : ∀ p ∈ P, p.Prime := smoothGiantPrimeRange_prime _
  have hPsub : P ⊆ Nat.primesLE (tailCollisionCutoff X) := by
    intro p hp
    have hpU := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have heq : lo + width + 2 + 1 = lo + width + 3 := by ring
    rw [heq] at hpU
    exact Nat.mem_primesLE.mpr ⟨hpU.trans hcut, hPprime p hp⟩
  have hbudgetAll := uniform_tail_collision_bound hA hB N (summandTailCutoff X) hi a X C
    ha hcuts.1 hcuts.2.1 hhi hcuts.2.2 (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
    (by simpa only [positiveSummandTail_card] using hsA)
    (by simpa only [negativeSummandTail_card] using hsB) hM.lower
  have hnon (p : ℕ) (hp : p ∈ Nat.primesLE (tailCollisionCutoff X)) :
      0 ≤ Real.log (p : ℝ) * tailCollisionDefect A N p E D
        (fun _ => (E.card : ℝ)⁻¹) (fun _ => (D.card : ℝ)⁻¹) := by
    apply mul_nonneg (Real.log_natCast_nonneg p)
    apply collisionDefect_nonneg
    · exact tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos
    · exact tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
        (hN p (Nat.prime_of_mem_primesLE hp))
    · exact (tailSupport_card_add_complement A N p).le
  have hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p E D
      (fun _ => (E.card : ℝ)⁻¹) (fun _ => (D.card : ℝ)⁻¹)) ≤ tailDefectBudget a C X := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun p hp _ => hnon p hp)).trans
    simpa only [tailDefectBudget, E, D, one_div] using hbudgetAll
  have hB0 : 0 ≤ tailDefectBudget a C X :=
    (Finset.sum_nonneg fun p hp => hnon p (hPsub hp)).trans hbudget
  obtain ⟨hlo5, hwidth, hupper, hsmall, hgeometry⟩ := hscale lo X hlo hhiLo hX hXhi
  obtain ⟨G, hGlo, hGhi, _, hmean⟩ := tail_giant_of_favorable_block hA hB N F E D
    (fun _ => (D.card : ℝ)⁻¹) lo width γ c (tailDefectBudget a C X) C hM hlo5
    (by dsimp [width]; positivity) hγ hc hB0 hwidth hupper
    (fun p hp => hN p (hPprime p hp)) hF hFbal hFγ
    (fun p hp x hx => by
      obtain ⟨hxA, hxlo, _⟩ := (mem_summandTail A _ _ x).mp hx
      refine ⟨hxA, ?_⟩
      have hple := Nat.le_of_mem_primesLE (hPsub hp)
      omega) hbudget hFmass hsmall
  obtain ⟨hGreserve, hG2, hGlower, hGupper⟩ := hgeometry G hGlo hGhi
  obtain ⟨hmass, hcg⟩ := hnorm G hG2 hGlower hGupper
  exact ⟨G, hGlo, hGreserve, hmass, hcg, hmean⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteLogBlockMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite weighted pigeonhole principle for logarithmic prime blocks -/
namespace Ostmann
open scoped Classical BigOperators

theorem logarithmic_block_reciprocal_bound (F : Finset ℕ) (j : ℕ) (w c : ℝ)
    (hw : 0 < w) (hlog : ∀ p ∈ F, w * (j + 1) ≤ Real.log (p : ℝ))
    (hweight : (∑ p ∈ F, Real.log (p : ℝ) / p) ≤ c * w) :
    (∑ p ∈ F, (p : ℝ)⁻¹) ≤ c / (j + 1) := by
  have hh : w * ((j + 1 : ℝ) * ∑ p ∈ F, (p : ℝ)⁻¹) ≤ c * w := by
    calc
      _ = ∑ p ∈ F, (w * (j + 1)) * (p : ℝ)⁻¹ := by rw [← Finset.mul_sum]; ring
      _ ≤ ∑ p ∈ F, Real.log (p : ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right (hlog p hp) (by positivity : 0 ≤ (p : ℝ)⁻¹)
      _ ≤ _ := hweight
  have hh' : (j + 1 : ℝ) * ∑ p ∈ F, (p : ℝ)⁻¹ ≤ c :=
    (mul_le_mul_iff_right₀ hw).mp (by nlinarith only [hh])
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < j + 1)).mpr
  nlinarith only [hh']

theorem exists_logarithmic_heavy_fiber (F : Finset ℕ) (key : ℕ → ℕ) (N : ℕ)
    (w c : ℝ) (hw : 0 < w) (hc : 0 ≤ c)
    (hkey : ∀ p ∈ F, key p < N)
    (hlog : ∀ p ∈ F, w * (key p + 1) ≤ Real.log (p : ℝ))
    (hmass : c * (1 + Real.log N) < ∑ p ∈ F, (p : ℝ)⁻¹) :
    ∃ j ∈ Finset.range N, c * w <
      ∑ p ∈ F.filter (fun p => key p = j), Real.log (p : ℝ) / p := by
  by_contra hn
  push Not at hn
  have hbound (j : ℕ) (hj : j ∈ Finset.range N) :
      (∑ p ∈ F.filter (fun p => key p = j), (p : ℝ)⁻¹) ≤ c / (j + 1) := by
    apply logarithmic_block_reciprocal_bound _ j w c hw
    · intro p hp
      obtain ⟨hpF, hpj⟩ := Finset.mem_filter.mp hp
      simpa only [hpj] using hlog p hpF
    · exact hn j hj
  have hfib : (∑ j ∈ Finset.range N, ∑ p ∈ F.filter (fun p => key p = j), (p : ℝ)⁻¹) =
      ∑ p ∈ F, (p : ℝ)⁻¹ :=
    Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_range.mpr (hkey p hp)) _
  have hh : (∑ p ∈ F, (p : ℝ)⁻¹) ≤ c * (1 + Real.log N) := by
    calc
      _ = ∑ j ∈ Finset.range N, ∑ p ∈ F.filter (fun p => key p = j), (p : ℝ)⁻¹ := hfib.symm
      _ ≤ ∑ j ∈ Finset.range N, c / (j + 1) := Finset.sum_le_sum hbound
      _ = c * (harmonic N : ℝ) := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Nat.cast_add,
          Nat.cast_one, div_eq_mul_inv, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) hc
  linarith

theorem exists_logarithmic_heavy_interval (F : Finset ℕ) (a b w c : ℝ)
    (hw : 0 < w) (hw1 : 1 ≤ w) (ha : w ≤ a) (hc : 0 ≤ c)
    (hF : ∀ p ∈ F, a ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ b)
    (hmass : c * (1 + Real.log (⌊b⌋₊ + 1 : ℕ)) < ∑ p ∈ F, (p : ℝ)⁻¹) :
    ∃ lo : ℝ, a ≤ lo ∧ lo ≤ b ∧
      c * w < ∑ p ∈ F.filter (fun p : ℕ => lo ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ lo + w),
        Real.log (p : ℝ) / p := by
  let key := fun p : ℕ => ⌊(Real.log (p : ℝ) - a) / w⌋₊
  have hcell (p : ℕ) (hp : p ∈ F) :
      a + key p * w ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) < a + key p * w + w := by
    have hnon : 0 ≤ (Real.log (p : ℝ) - a) / w := div_nonneg (by linarith [(hF p hp).1]) hw.le
    have hlow := (le_div_iff₀ hw).mp (Nat.floor_le hnon)
    have hhigh := (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one ((Real.log (p : ℝ) - a) / w))
    dsimp [key]
    constructor <;> nlinarith
  have hkey (p : ℕ) (hp : p ∈ F) : key p < ⌊b⌋₊ + 1 := by
    have hk0 : (0 : ℝ) ≤ key p := Nat.cast_nonneg _
    have hlog0 : 0 ≤ Real.log (p : ℝ) := by linarith [(hF p hp).1]
    have hk : (key p : ℝ) ≤ Real.log (p : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hw1 hk0
      linarith [(hcell p hp).1]
    exact Nat.lt_succ_of_le (Nat.le_floor (hk.trans (hF p hp).2))
  obtain ⟨j, _, hj⟩ := exists_logarithmic_heavy_fiber F key (⌊b⌋₊ + 1) w c hw hc hkey
    (fun p hp => by nlinarith [(hcell p hp).1]) hmass
  have hne : (F.filter (fun p => key p = j)).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    rw [hn, Finset.sum_empty] at hj
    exact (not_lt_of_ge (mul_nonneg hc hw.le)) hj
  obtain ⟨p, hp⟩ := hne
  obtain ⟨hpF, hpj⟩ := Finset.mem_filter.mp hp
  refine ⟨a + j * w, le_add_of_nonneg_right (by positivity), ?_, hj.trans_le ?_⟩
  · have hh := (hcell p hpF).1
    rw [hpj] at hh
    exact hh.trans (hF p hpF).2
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨hqF, hqj⟩ := Finset.mem_filter.mp hq
      refine Finset.mem_filter.mpr ⟨hqF, ?_⟩
      have hh := hcell q hqF
      rw [hqj] at hh
      exact ⟨hh.1, hh.2.le⟩
    · intro q hq _
      exact div_nonneg (by linarith [(hF q (Finset.mem_filter.mp hq).1).1]) (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FavorableBlockSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting one dense logarithmic block from the favorable prime mass -/
namespace Ostmann
open scoped Classical BigOperators

theorem favorable_logarithmic_block (L : ℝ) (hL : 1000 ≤ L) (F : Finset ℕ)
    (hF : F ⊆ logLogPrimeBand L)
    (hmass : (3 / 20 : ℝ) * L < ∑ p ∈ F, (p : ℝ)⁻¹) :
    ∃ lo : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo ∧
      lo ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
      (1 / 20 : ℝ) * (10 * Real.exp ((1 / 100 : ℝ) * L)) <
        ∑ p ∈ F.filter (fun p : ℕ => lo ≤ Real.log (p : ℝ) ∧
          Real.log (p : ℝ) ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L)), Real.log (p : ℝ) / p := by
  have hL0 : 0 ≤ L := by linarith
  have hw1 : 1 ≤ 10 * Real.exp ((1 / 100 : ℝ) * L) := by
    have he := Real.one_le_exp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100) hL0)
    linarith
  have ha : 10 * Real.exp ((1 / 100 : ℝ) * L) ≤ Real.exp ((1 / 20 : ℝ) * L) := by
    have hten : 10 ≤ Real.exp ((1 / 25 : ℝ) * L) := by
      linarith [Real.add_one_le_exp ((1 / 25 : ℝ) * L)]
    have hh := mul_le_mul_of_nonneg_right hten (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    rw [← Real.exp_add] at hh
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
  have hlogN : Real.log (⌊Real.exp ((9 / 10 : ℝ) * L)⌋₊ + 1 : ℕ) ≤ L := by
    have hb : 1 ≤ Real.exp ((9 / 10 : ℝ) * L) := Real.one_le_exp (by positivity)
    have htwo : 2 ≤ Real.exp ((1 / 10 : ℝ) * L) := by
      linarith [Real.add_one_le_exp ((1 / 10 : ℝ) * L)]
    have hh := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    rw [← Real.exp_add, show (9 / 10 : ℝ) * L + (1 / 10 : ℝ) * L = L by ring] at hh
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have hf := Nat.floor_le (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    push_cast
    linarith
  apply exists_logarithmic_heavy_interval F (Real.exp ((1 / 20 : ℝ) * L))
    (Real.exp ((9 / 10 : ℝ) * L)) (10 * Real.exp ((1 / 100 : ℝ) * L))
    (1 / 20) (by positivity) hw1 ha (by norm_num)
  · intro p hp
    exact ⟨(logLogPrimeBand_mem (hF hp)).2.1.le, (logLogPrimeBand_mem (hF hp)).2.2⟩
  · apply lt_trans _ hmass
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedEndpointGiant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant with the endpoint chosen from its favorable block -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.selected_endpoint_giant
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) :
    ∃ N : ℕ, (∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q)) ∧
      ∀ k : ℕ, ∀ᶠ reference : ℕ in atTop,
        let L := Real.log (Real.log (reference : ℝ))
        ∃ lo : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo ∧ lo ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
        ∃ F : Finset ℕ, F ⊆ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
          (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2) ∧
        ∃ Y : ℝ, ∃ hi : ℕ, (hi : ℝ) = Real.exp Y ∧
          2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y ∧
          Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 ∧
          Real.exp ((4 / 100 : ℝ) * L) ≤ Y ∧ Y ≤ Real.exp L ∧
        ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ (lo - 2) + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
          Real.exp (-(91 / 100 : ℝ) * L) ≤ smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
          smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100 : ℝ) * L ∧
          ((1 / 1000000 : ℝ) ^ 2 * (1 / 20) / 32) <
            ∑ p : smoothGiantPrimeRange G,
              smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p *
                tailGiantEndpointMean A N F (summandTail A (summandTailCutoff Y) hi) p := by
  obtain ⟨N, hN, hfav⟩ := h.favorable_tail_prime_mass ls hsize hA hB CM CH hM hMH Z hD hR P hPNT
  obtain ⟨_a, _, hgiant⟩ := h.eventual_giant_from_favorable_blocks P0 hsize hA hB N hN
    CM ((1 / 1000000 : ℝ) ^ 2) (1 / 20) hM (by norm_num) (by norm_num)
  have ht : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨N, hN, fun k => ?_⟩
  filter_upwards [ht.eventually hfav, ht.eventually hgiant,
    ht.eventually (eventual_favorable_block_endpoint k),
    ht.eventually (eventually_ge_atTop (1000 : ℝ)), eventually_ge_atTop (3 : ℕ)]
    with reference hfav hgiant hgeo hL href
  let L := Real.log (Real.log (reference : ℝ))
  have href3 : (3 : ℝ) ≤ reference := by exact_mod_cast href
  have href0 : (0 : ℝ) < reference := by linarith
  have hlog : 0 < Real.log (reference : ℝ) := Real.log_pos (by linarith)
  have hX : (reference : ℝ) = Real.exp (Real.exp L) := by
    dsimp [L]
    rw [Real.exp_log hlog, Real.exp_log href0]
  dsimp only
  let F0 := favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
    (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2)
  have hF0 : F0 ⊆ logLogPrimeBand L := Finset.filter_subset _ _
  obtain ⟨lo, hlo, hhiLo, hmass⟩ := favorable_logarithmic_block L hL F0 hF0 (hfav reference hX)
  let F := F0.filter (fun p : ℕ => lo ≤ Real.log (p : ℝ) ∧
    Real.log (p : ℝ) ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L))
  have hFF (p : ℕ) (hp : p ∈ F) : p ∈ F0 := (Finset.mem_filter.mp hp).1
  have hFp (p : ℕ) (hp : p ∈ F) : p.Prime := (logLogPrimeBand_mem (hF0 (hFF p hp))).1
  have hFb (p : ℕ) (hp : p ∈ F) :
      p.Prime ∧ lo ≤ Real.log p ∧ Real.log p ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L) :=
    ⟨hFp p hp, (Finset.mem_filter.mp hp).2⟩
  have hbal (p : ℕ) (hp : p ∈ F) : ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3 :=
    (Finset.mem_filter.mp (hFF p hp)).2.2.1
  have hγ (p : ℕ) (hp : p ∈ F) : let _ : Fact p.Prime := ⟨hFp p hp⟩;
      (1 / 1000000 : ℝ) ^ 2 ≤
        (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖ := by
    dsimp only
    let : NeZero p := ⟨(hFp p hp).ne_zero⟩
    rw [← tailFourierMass_eq A N p]
    exact (Finset.mem_filter.mp (hFF p hp)).2.2.2
  obtain ⟨Y, hi, hhi, hYlo, hYhi, hYmin, hYmax, hcut⟩ :=
    hgeo lo (by simpa only [L, show (1 / 20 : ℝ) = 5 / 100 by norm_num] using hlo) hhiLo
  obtain ⟨G, hGlo, hGhi, hmassG, hnormG, hmean⟩ := hgiant Y hYmin hYmax hi hhi
    lo (by simpa only [L, show (1 / 20 : ℝ) = 5 / 100 by norm_num] using hlo) hhiLo hcut F hFb hbal hγ hmass.le
  exact ⟨lo, hlo, hhiLo, F, fun p hp => hFF p hp, Y, hi, hhi, hYlo, hYhi, hYmin, hYmax,
    G, hGlo, hGhi, hmassG, hnormG, hmean⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantActiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size and separation on the support of the smooth giant law -/

namespace Ostmann

theorem smoothGiantPrior_active_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : P) (hp : smoothGiantPrior P φ G p ≠ 0) :
    Real.exp (G - 1) < (p : ℝ) ∧ (p : ℝ) < Real.exp (G + 1) := by
  have hφ : φ (Real.log (p : ℕ) - G) ≠ 0 := by
    intro h
    apply hp
    simp only [smoothGiantPrior, h, mul_zero, zero_div]
  have habs : |Real.log (p : ℕ) - G| < 1 := lt_of_not_ge (fun h => hφ (hout _ h))
  have hpos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (hP _ p.property).pos
  constructor
  · apply (Real.exp_lt_exp.mpr (show G - 1 < Real.log (p : ℕ) by linarith [(abs_lt.mp habs).1])).trans_eq
    exact Real.exp_log hpos
  · rw [← Real.exp_log hpos]
    exact Real.exp_lt_exp.mpr (by linarith [(abs_lt.mp habs).2])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialPrimeLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower endpoints for every live prime in the original initial prior -/
namespace Ostmann
open Filter
open scoped Classical

theorem initial_selected_centers_lower
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target H : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (hHtop : H ≤ target) (hHcenters : ∀ w ∈ targets, H ≤ w / 4) :
    ∀ j ∈ initialSmallCellList top centers, H ≤ (j : ℝ) := by
  apply initialSmallCellList_property top centers (fun j => H ≤ (j : ℝ))
    (hHtop.trans htop.1)
  induction hcenters with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hHcenters w (by simp)).trans hj.1
    · exact ih (fun v hv => hHcenters v (by simp [hv])) i hi

theorem selected_initial_prior_lower
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G target H : ℝ}
    {D Qb Qd : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (b d : ℕ)
    (hG : H + 1 ≤ G) (hb : ∀ p ∈ Qb, Real.exp H ≤ (p : ℝ))
    (hd : ∀ p ∈ Qd, Real.exp H ≤ (p : ℝ))
    (hc : ∀ j ∈ initialSmallCellList top centers, H ≤ (j : ℝ)) :
    ∀ i (p : P), selectedInitialHalfPrior P A B N hi Y G D Qb Qd b d top centers i p ≠ 0 →
      Real.exp H ≤ (p : ℝ) := by
  have hcell (i : Fin (initialSmallCellList top centers).length) (p : P)
      (hp : primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D
        ((initialSmallCellList top centers).get i)) p ≠ 0) : Real.exp H ≤ (p : ℝ) := by
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcenters _
      (List.get_mem (initialSmallCellList top centers) i)
    have hs := ht.2.2.2.2.2.2 p (primeSubsetPrior_support P _ p hp)
    exact (Real.exp_le_exp.mpr (hc _ (List.get_mem _ i))).trans hs.2.1.le
  intro i p
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hp
    have hs := smoothGiantPrior_active_bounds P hP logCellProfile G
      logCellProfile_zero_outside p hp
    exact (Real.exp_le_exp.mpr (by linarith : H ≤ G - 1)).trans hs.1.le
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [selectedInitialHalfPrior, Fin.cons_succ, Fin.append_left]
      exact fun hp => hb p (primeSubsetPrior_support P Qb p hp)
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right, Fin.append_left]
        exact fun hp => hd p (primeSubsetPrior_support P Qd p hp)
      · simpa only [selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right] using hcell j p

theorem eventual_initial_selected_centers_lower (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ} {a C Y G lo : ℝ}
      {D : Finset ℕ} {centers : List ℕ} (cb cd : ℤ),
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        centers (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) →
      ∀ j ∈ initialSmallCellList top centers, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ) := by
  filter_upwards [eventual_initial_protected_target k hk Bs BD Bz hBs hBD hBz,
    eventual_protected_cell_target_range,
    eventual_prescribed_compensation_range k (by omega) BD Bz hBD hBz]
    with L hprotected htopRange hcompRange
  intro A B N hi top a C Y G lo D centers cb cd hcb hcd hYlo hYhi hGlo hGhi htop hcenters
  obtain ⟨hJlo, hJhi, hcb0, hcbJ⟩ := hprotected cb cd hcb hcd lo G Y hYlo hYhi hGlo hGhi
  apply initial_selected_centers_lower htop hcenters
    (htopRange _ _ hJlo hJhi hcb0 hcbJ).1
  intro w hw
  exact (hcompRange _ hJlo hJhi w hw).1

theorem eventual_selected_initial_prime_lower (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ} {a C Y G lo : ℝ}
      {D Qd : Finset ℕ} {centers : List ℕ} (cb cd : ℤ),
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      Real.exp ((1 / 20 : ℝ) * L) ≤ lo →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
        (Real.exp ((6 / 10000 : ℝ) * L)) \ D →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        centers (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) →
      ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ b d : ℕ,
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      ∀ i (p : P), selectedInitialHalfPrior P A B N hi Y G D Qb Qd b d top centers i p ≠ 0 →
        Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ (p : ℝ) := by
  have ht : Tendsto (fun L : ℝ => Real.exp (((1 / 20 : ℝ) - 4 / 10000) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [eventual_initial_selected_centers_lower k hk Bs BD Bz hBs hBD hBz,
    ht.eventually (eventually_ge_atTop (4 : ℝ)), eventually_ge_atTop (0 : ℝ)]
    with L hcentersLower hratio hL
  intro A B N hi top a C Y G lo D Qd centers cb cd hcb hcd hYlo hYhi hlo hGlo hGhi
    hQd htop hcenters P hP b d Qb
  have hr := mul_le_mul_of_nonneg_right hratio
    (Real.exp_nonneg ((4 / 10000 : ℝ) * L))
  rw [← Real.exp_add] at hr
  have he : ((1 / 20 : ℝ) - 4 / 10000) * L + (4 / 10000) * L = (1 / 20) * L := by ring
  rw [he] at hr
  have hsmall : 1 ≤ Real.exp ((4 / 10000 : ℝ) * L) := Real.one_le_exp (by positivity)
  have hG : Real.exp ((4 / 10000 : ℝ) * L) + 1 ≤ G := by linarith
  apply selected_initial_prior_lower htop hcenters P hP b d hG
  · intro p hp
    have hs := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
    have hh := (Real.lt_log_iff_exp_lt (by exact_mod_cast hs.1.pos)).mp hs.2.2.1
    exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))).trans hh.le
  · intro p hp
    have hs := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQd hp)).1
    exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast hs.1.pos)).mp hs.2.2.1).le
  · intro j hj
    exact (Real.exp_le_exp.mpr (by linarith : (4 / 10000 : ℝ) * L ≤ (1 / 100) * L)).trans
      (hcentersLower cb cd hcb hcd hYlo hYhi hGlo hGhi htop hcenters j hj)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailCutoffHarmonicMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic cost of the full ambient prime set -/
namespace Ostmann
open scoped Classical BigOperators

theorem MertensHarmonicEstimate.tail_cutoff_mass {C : ℝ} (hM : MertensHarmonicEstimate C)
    (Y L : ℝ) (hY : 1 ≤ Y) (hcut : 2 ≤ Real.exp (Y / 2) / Y ^ 5)
    (hYL : Y ≤ Real.exp L) :
    (∑ p ∈ Nat.primesLE (tailCollisionCutoff Y), (p : ℝ)⁻¹) ≤ L + C := by
  have hY0 : 0 < Y := by linarith
  have hQ2 : 2 ≤ tailCollisionCutoff Y := Nat.le_floor hcut
  have hQ0 : (0 : ℝ) < tailCollisionCutoff Y := by exact_mod_cast (show 0 < tailCollisionCutoff Y by omega)
  have hQ : (tailCollisionCutoff Y : ℝ) ≤ Real.exp Y := by
    apply (tailCollisionCutoff_bounds Y hY hcut).2.1.trans
    apply (div_le_self (Real.exp_nonneg _) (one_le_pow₀ hY)).trans
    exact Real.exp_le_exp.mpr (by linarith)
  have hlogQ : Real.log (tailCollisionCutoff Y : ℝ) ≤ Y :=
    (Real.log_le_iff_le_exp hQ0).mpr hQ
  have hlogQ0 : 0 < Real.log (tailCollisionCutoff Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < tailCollisionCutoff Y by omega))
  have hlogY : Real.log Y ≤ L := (Real.log_le_iff_le_exp hY0).mpr hYL
  have hh := (abs_le.mp (hM _ hQ2)).2
  have hlogs := Real.log_le_log hlogQ0 hlogQ
  linarith

theorem MertensHarmonicEstimate.tail_cutoff_mass_linear {C : ℝ} (hM : MertensHarmonicEstimate C)
    (Y L : ℝ) (m : ℕ) (hY : 1 ≤ Y) (hcut : 2 ≤ Real.exp (Y / 2) / Y ^ 5)
    (hYL : Y ≤ Real.exp L) (hC : C ≤ L) (hm : L ≤ m) :
    (∑ p : Nat.primesLE (tailCollisionCutoff Y), (p : ℝ)⁻¹) ≤ 2 * m := by
  have hh := hM.tail_cutoff_mass Y L hY hcut hYL
  have he : (∑ p : Nat.primesLE (tailCollisionCutoff Y), (p : ℝ)⁻¹) =
      ∑ p ∈ Nat.primesLE (tailCollisionCutoff Y), (p : ℝ)⁻¹ := by
    exact Finset.sum_coe_sort (Nat.primesLE (tailCollisionCutoff Y)) (fun p : ℕ => (p : ℝ)⁻¹)
  rw [he]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the original positive initial amplitude from published inputs -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem EventuallyPrimeSumset.constructed_initial_amplitude_oai
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT)
    (ψ : 𝓢(ℝ, ℂ)) (H c : ℝ) (hH : 0 ≤ H) (hc : 0 < c)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (hψlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ t).re) :
    ∃ N : ℕ, ∃ a : ℝ, 0 < a ∧
      (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      ∀ k : ℕ, 2 ≤ k → ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
      2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
        (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1 →
      14 * (64 * tailCellLinearRate a CM + 3) ≤ (k : ℝ) ^ 3 →
      ∀ cutoff : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ reference : ℕ in atTop,
      let L := Real.log (Real.log (reference : ℝ))
      ∃ lo : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo ∧ lo ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
      ∃ F : Finset ℕ, F ⊆ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
        (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2) ∧
      ∃ Y : ℝ, ∃ hi : ℕ, (hi : ℝ) = Real.exp Y ∧
        2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y ∧
        Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 ∧
        Real.exp ((4 / 100 : ℝ) * L) ≤ Y ∧ Y ≤ Real.exp L ∧
      ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
        Real.exp (-(91 / 100 : ℝ) * L) ≤
          smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
        smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L ∧
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ Qd : Finset ℕ, ∃ cb cd : ℤ, ∃ top : ℕ, ∃ centers : List ℕ,
        Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
        (∀ p ∈ Qd, cutoff ≤ p ∧
          ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
            residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧ tailCharacterBias A N p ≤ ε / 2) ∧
        cb ∈ Finset.Icc (0 : ℤ)
          ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ ∧
        cd ∈ Finset.Icc (0 : ℤ)
          ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ ∧
        SelectedSmallTailCell A B N a CM L Y hi D
          ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a CM L Y hi D (w / 4) j)
          centers (movingCompensationTargets
            (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
            (movingCompensationGaps k BD Bz L)) ∧ centers.length = k ∧
        let P := Nat.primesLE (tailCollisionCutoff Y)
        let _ : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(Nat.prime_of_mem_primesLE p.property).ne_zero⟩
        let m := spectatorBulkCount k L
        let cells := initialSmallCellList top centers
        let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
          (Real.exp ((6 / 1000 : ℝ) * L)) \ D
        let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd (m / 2) (m / 2) top centers
        let w := initialHalfCutoffWeight (fun p : P => (p : ℕ)) (m / 2) (m / 2) cells.length cb cd
        let Δ := selectedInitialLogCenter G Y cb cd top centers
        let width : ℝ := 2 * (cells.length + 3)
        ∀ T : ℕ → ℝ,
        let V := movingProductNaturalCutoff T (Y + Δ + width) Y ((m : ℝ) / 4) 0
        let Ftest : Fin ((m / 2 + (m / 2 + cells.length)) + 1) →
          (p : P) → ZMod (p : ℕ) → ℂ :=
            primeHalfTests P (fun p => tailDensityMask A N p) (fun p => decide ((p : ℕ) ∈ F))
        Real.exp (-(6 * Real.log 2 + 13) * m) ≤
          ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append Ftest Ftest) ψ (Real.exp Y) V
            (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ)))‖ ∧
        ∃ sl sr : Fin (m / 2) → P, Function.Injective (Fin.append sl sr) ∧
          (∀ i, (sl i : ℕ) ∈ Qd) ∧ (∀ i, (sr i : ℕ) ∈ Qd) ∧
          Real.exp (-(6 * Real.log 2 + 13) * m) ≤
            ‖initialFrozenAmplitude P (m / 2) (m / 2) cells.length
              (smoothGiantPrior P logCellProfile G) (fun _ => primeSubsetPrior P Qb)
              (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D (cells.get i)))
              (Fin.append Ftest Ftest) ψ (Real.exp Y) V
              (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ))) sl sr‖ := by
  classical
  obtain ⟨N, hN, hgiant⟩ := h.selected_endpoint_giant P0 ls hsize hA hB CM CH hM hMH
    Z hD hR Pexplicit hPNT
  obtain ⟨a, ha, hnongiant⟩ := h.constructed_initial_nongiant_priors hBonami P0 Hreal
    hSiegel sieve hsize hM hA hB N hN
  obtain ⟨atail, hatail, htail⟩ := h.initial_tail_endpoint hsize hA hB N
  have ht : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have hYlarge : ∀ᶠ L : ℝ in atTop, Y₀ ≤ Real.exp ((4 / 100 : ℝ) * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))).eventually
      (eventually_ge_atTop Y₀)
  refine ⟨N, a, ha, hN, ?_⟩
  intro k hk Bs BD Bz hBs hBD hBz hgap hklarge cutoff ε hε
  have hamp := eventual_selected_initial_amplitude k hk Bs BD Bz a CM atail c
    ((1 / 1000000 : ℝ) ^ 2 * (1 / 20) / 32) H hBs hH hatail hc (by norm_num)
    hgap hklarge ψ hψ hsupp
  filter_upwards [hgiant k, ht.eventually (hnongiant k hk Bs BD Bz hBs hBD hBz cutoff ε hε),
    ht.eventually hamp, ht.eventually eventual_initial_regular_prime_range,
    ht.eventually (eventual_initial_giant_prime_range k hk),
    ht.eventually (eventual_selected_initial_prime_lower k hk Bs BD Bz hBs hBD hBz),
    ht.eventually htail, ht.eventually hYlarge,
    ht.eventually (eventually_ge_atTop (max 1 CH))]
    with reference hgiant hnongiant hamp hsmall hbig hprimelow htail hYlarge hL
  dsimp only at hgiant ⊢
  let L := Real.log (Real.log (reference : ℝ))
  obtain ⟨lo, hlo, hlohi, F, hF, Y, hi, hhi, hYlo', hYhi', hYlo, hYhi,
    G, hGlo, hGhi, hmass, hnorm, hmean⟩ := hgiant
  refine ⟨lo, hlo, hlohi, F, hF, Y, hi, hhi, hYlo', hYhi', hYlo, hYhi,
    G, hGlo, hGhi, hmass, hnorm, ?_⟩
  intro D hDcard
  let P := Nat.primesLE (tailCollisionCutoff Y)
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => Nat.prime_of_mem_primesLE hp
  have hsmallP : initialRegularPrimeRange L ⊆ P := hsmall Y hYlo hYhi
  have hgiantP : smoothGiantPrimeRange G ⊆ P := hbig lo Y G hYlo hYhi hYlo' hGhi
  obtain ⟨Qd, cb, cd, top, centers, hQd, hQmass, hgood, hcb, hcd, htop, hcenters,
    hlen, _htotal, hb, hd, hpoint, hbalanced⟩ :=
    hnongiant Y hYlo hYhi hi hhi lo G hYlo' hYhi' hGlo hGhi D hDcard P hP hsmallP
  refine ⟨Qd, cb, cd, top, centers, hQd, hQmass, hgood, hcb, hcd, htop, hcenters, hlen, ?_⟩
  let : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hP p p.property).ne_zero⟩
  let m := spectatorBulkCount k L
  intro T
  have hend := htail Y hYlo hYhi hi hhi
  have hcut := hY₀ Y (hYlarge.trans hYlo)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hCH : CH ≤ L := (le_max_right _ _).trans hL
  have hYpos : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
    norm_num at hh
    nlinarith
  have hmlo : L ≤ (m : ℝ) := by
    have hh := spectatorBulkCount_half k L hscale
    have hp : (2 : ℝ) ≤ (k : ℝ) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
      norm_num at hh
      linarith
    nlinarith only [hh, mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ L)]
  have htotal := hMH.tail_cutoff_mass_linear Y L m hcut.1 hcut.2.1 hYhi hCH hmlo
  have hmean' := ambient_tail_giant_endpoint_lower A N F
    (summandTail A (summandTailCutoff Y) hi) P hP G
    ((1 / 1000000 : ℝ) ^ 2 * (1 / 20) / 32) hgiantP
    (by simpa only [positiveSummandTail, Finset.image_nonempty] using hend.2.1) hmean.le
  have hlower := hamp hYpos hYhi htop hcenters hlen P hP hsmallP hgiantP
    ((Real.exp_pos _).trans_le hmass) hnorm hb hd hpoint
    (by simpa only [selectedInitialHalfPrior, Fin.tail_cons, initialHalfCutoffWeight,
      mul_assoc] using hbalanced)
    (hprimelow cb cd hcb hcd hYlo' hYhi' hlo hGlo hGhi hQd htop hcenters P hP (m / 2) (m / 2))
    htotal (positiveSummandTail A (summandTailCutoff Y) hi)
    (fun p => decide ((p : ℕ) ∈ F)) hend.1 (fun e he => hψlower _ (hend.2.2.1 e he))
    hend.2.2.2 hmean' T
  refine ⟨hlower, ?_⟩
  obtain ⟨sl, sr, hinj, hsl, hsr, hfrozen⟩ := exists_distinct_initial_spectators P
    (m / 2) (m / 2) (initialSmallCellList top centers).length
    (smoothGiantPrior P logCellProfile G)
    (fun _ => primeSubsetPrior P
      (primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D))
    (fun _ => primeSubsetPrior P Qd)
    (fun i => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y hi D ((initialSmallCellList top centers).get i)))
    (fun _ => primeSubsetPrior_nonneg P Qd) (fun _ => hd) _ ψ (Real.exp Y) _ _
    (Real.exp (-(6 * Real.log 2 + 13) * m)) (Real.exp_pos _) hlower
  exact ⟨sl, sr, hinj, fun i => primeSubsetPrior_support P Qd (sl i) (hsl i),
    fun i => primeSubsetPrior_support P Qd (sr i) (hsr i), hfrozen⟩

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude_oai := @OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude_oai
