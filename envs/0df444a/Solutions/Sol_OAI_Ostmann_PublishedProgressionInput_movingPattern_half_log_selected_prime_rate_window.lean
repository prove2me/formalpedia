-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_selected_prime_rate_window
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:24:02.567648+00:00
-- url     : https://prove2.me/submissions/aa396e57-b530-4eb0-a213-8253d044bd7a

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_log_mixed_prime_signed_bound
import Theorems.Thm_OAI_Ostmann_exists_movingPatternPrimeGain_window

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeCellPartitionConstruction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the actual prime log/residue partition

The fiber identities used by the joint comparison follow from separated
log intervals and residue classes. They are not additional distribution
hypotheses.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem primeLogCellSet_disjoint (q a b : ℕ) (s t u v : ℝ)
    (hsep : ¬Nat.ModEq q a b ∨ t ≤ u ∨ v ≤ s) :
    Disjoint (primeLogCellSet q a s t) (primeLogCellSet q b u v) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨hpI, hpP, hpA⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpJ, _, hpB⟩ := Finset.mem_filter.mp hp'
  have hi := log_mem_of_mem_exp_interval hpI
  have hj := log_mem_of_mem_exp_interval hpJ
  rcases hsep with hres | htu | hvs
  · exact hres (hpA.symm.trans hpB)
  · linarith [hi.2, hj.1]
  · linarith [hj.2, hi.1]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_OrdinaryPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordinary prime interval and its normalization

The conductor-one character is trivial, so the ordinary prime prior has
no Page correction. Its logarithmic interval mass and inverse bound are
derived from the same published theta input.
-/

namespace Ostmann

open Filter MeasureTheory

theorem PublishedProgressionInput.localZero_one (P : PublishedProgressionInput) :
    P.localZero 1 = none := by
  cases he : P.localZero 1 with
  | none => rfl
  | some e => exact False.elim (e.modulus_ne_one (Nat.dvd_one.mp (P.divides 1 e he)))

theorem PublishedProgressionInput.ordinary_log_interval (P : PublishedProgressionInput)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp t) - Real.log (t / s)| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) := by
  have h := P.local_log_interval 1 0 (by norm_num) (by norm_num) hs hst hshort
  rw [P.localZero_one] at h
  simp only [pageCoefficient, pageBeta, Nat.totient_one, Nat.cast_one,
    primeLogDensity, zero_mul, sub_zero, one_mul] at h
  rw [← intervalIntegral.integral_of_le hst,
    integral_one_div_of_pos (by linarith) (by linarith)] at h
  exact h

theorem theta_log_error_small (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ s : ℝ in atTop,
      18 * C * Real.exp (-c * Real.sqrt s) ≤ 1 / (2 * (s + 1)) := by
  have hpow := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).comp
    Real.tendsto_sqrt_atTop
  have hlin : Tendsto (fun s : ℝ => s * Real.exp (-c * Real.sqrt s)) atTop (nhds 0) := by
    apply hpow.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    dsimp only [Function.comp_def]
    rw [Real.rpow_two, Real.sq_sqrt hs]
  have hzero := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc).comp
    Real.tendsto_sqrt_atTop
  simp only [Real.rpow_zero, one_mul, Function.comp_def] at hzero
  have hsum : Tendsto (fun s : ℝ =>
      (s + 1) * (18 * C * Real.exp (-c * Real.sqrt s))) atTop (nhds 0) := by
    have hb : Tendsto (fun s : ℝ => 18 * C *
        (s * Real.exp (-c * Real.sqrt s) + Real.exp (-c * Real.sqrt s))) atTop (nhds 0) := by
      simpa only [add_zero, mul_zero] using ((hlin.add hzero).const_mul (18 * C))
    exact hb.congr (fun s => by ring)
  filter_upwards [hsum.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℝ)] with s hsmall hs
  apply (le_div_iff₀ (by positivity : 0 < 2 * (s + 1))).mpr
  nlinarith

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

theorem log_unit_ratio_upper {s : ℝ} (hs : 0 < s) :
    Real.log ((s + 1) / s) ≤ 1 / s := by
  have hh := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < s + 1) hs)
  have heq : (s + 1) / s - 1 = 1 / s := by field_simp; ring
  rwa [heq] at hh

theorem PublishedProgressionInput.ordinary_interval_upper (P : PublishedProgressionInput) :
    ∀ᶠ s : ℝ in atTop,
      reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp (s + 1)) ≤ 2 / s := by
  filter_upwards [theta_log_error_small P.errorConstant P.decay P.decay_pos,
    eventually_ge_atTop (1 : ℝ)] with s herr hs
  have hmain := P.ordinary_log_interval hs (by linarith : s ≤ s + 1) le_rfl
  have hlog := log_unit_ratio_upper (by linarith : 0 < s)
  have herror : 1 / (2 * (s + 1)) ≤ 1 / s :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h := (abs_le.mp hmain).2
  rw [show 2 / s = 1 / s + 1 / s by ring]
  linarith

theorem sum_primeLogCellSet_reciprocal (q a : ℕ) (s t : ℝ) :
    (∑ p ∈ primeLogCellSet q a s t, (p : ℝ)⁻¹) =
      reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) := by
  simp only [primeLogCellSet, Finset.sum_filter, reciprocalPrimeInterval]

/-- Every subset of the actual prime cell has reciprocal mass `O(1/s)`,
uniformly in the subset. -/
theorem PublishedProgressionInput.prime_log_cell_upper (P : PublishedProgressionInput) :
    ∀ᶠ s : ℝ in atTop, ∀ E : Finset ℕ,
      E ⊆ primeLogCellSet 1 0 s (s + 1) → (∑ p ∈ E, (p : ℝ)⁻¹) ≤ 2 / s := by
  filter_upwards [P.ordinary_interval_upper] with s hs E hE
  calc
    _ ≤ ∑ p ∈ primeLogCellSet 1 0 s (s + 1), (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun p _ _ => by positivity)
    _ ≤ 2 / s := by rw [sum_primeLogCellSet_reciprocal]; exact hs

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem primeSubsetPrior_mass (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) : (∑ p : P, primeSubsetPrior P Q p) = 1 := by
  unfold primeSubsetPrior
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, ← Finset.sum_div]
  exact div_self hm

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth cost of the constructed Fourier variation bound -/

namespace Ostmann
open scoped SchwartzMap

/-- Uniform in moving endpoints whose width has the actual exponential scale. -/
theorem movingFourierVariationBudget_exp_window (ψ : 𝓢(ℝ, ℂ)) (n : ℕ)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) →
      movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ≤
        Real.exp (C * (m + 1)) := by
  let B := SchwartzMap.seminorm ℝ 0 0 ψ
  let D := SchwartzMap.seminorm ℝ 0 1 ψ
  let K := 3 * B + D
  let r : ℝ := (2 ^ n : ℕ)
  have hB : 0 ≤ B := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD : 0 ≤ D := schwartz_profile_lip_nonneg ψ
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  refine ⟨r * (K + A + H + 1), by positivity, ?_⟩
  intro m hm lo hi hhi hwidth
  have heA : 1 ≤ Real.exp (A * m) := Real.one_le_exp_iff.mpr (mul_nonneg hA hm)
  have heH : 1 ≤ Real.exp (H * m) := Real.one_le_exp_iff.mpr (mul_nonneg hH hm)
  have heAll : Real.exp (A * m) * Real.exp (H * m) = Real.exp ((A + H) * m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hproduct : 1 ≤ Real.exp (A * m) * Real.exp (H * m) :=
    heH.trans (le_mul_of_one_le_left (Real.exp_nonneg _) heA)
  have hHproduct : Real.exp (H * m) ≤ Real.exp (A * m) * Real.exp (H * m) :=
    le_mul_of_one_le_left (Real.exp_nonneg _) heA
  have hpoly : 2 * B + (B + D * Real.exp (A * m)) * (hi - lo) ≤
      K * Real.exp ((A + H) * m) := by
    calc
      _ ≤ 2 * B + (B + D * Real.exp (A * m)) * Real.exp (H * m) := by gcongr
      _ ≤ K * (Real.exp (A * m) * Real.exp (H * m)) := by
        dsimp only [K]
        nlinarith [mul_le_mul_of_nonneg_left hproduct hB,
          mul_le_mul_of_nonneg_left hHproduct hB]
      _ = _ := by rw [heAll]
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hbase : 2 * B + (B + D * Real.exp (A * m)) * (hi - lo) ≤
      Real.exp (K + (A + H) * m) := by
    rw [Real.exp_add]
    exact hpoly.trans (mul_le_mul_of_nonneg_right hKe (Real.exp_nonneg _))
  unfold movingFourierVariationBudget
  change (2 * B + (B + D * Real.exp (A * m)) * (hi - lo)) ^ (2 ^ n) ≤ _
  apply (pow_le_pow_left₀ (by positivity) hbase (2 ^ n)).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  change r * (K + (A + H) * m) ≤ r * (K + A + H + 1) * (m + 1)
  nlinarith [mul_nonneg hK hm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealSlotEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real bulk coordinates in the original smooth moving tree -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem realSlotProduct_nat {σ : Type*} (value : σ → ℕ) (slots : List σ) :
    realSlotProduct (fun j => (value j : ℝ)) slots =
      (MovingSlotReversal.naturalProduct value slots : ℝ) := by
  induction slots with
  | nil => simp [realSlotProduct, MovingSlotReversal.naturalProduct]
  | cons j slots ih => simpa only [realSlotProduct, MovingSlotReversal.naturalProduct,
      List.map_cons, List.prod_cons, Nat.cast_mul] using congrArg ((value j : ℝ) * ·) ih

theorem MovingSlotReversal.realValuePivot_nat {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (L R : ℝ) :
    s.realValuePivot (fun j => (value j : ℝ)) L R = s.realPivot value L R := by
  simp only [realValuePivot, realPivot, realSlotProduct_nat]

theorem MovingSlotData.realValueLeafModuli_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) (j : TreeLeafIndex n) :
    T.realValueLeafModuli (fun i => (value i : ℝ)) L R j = T.realLeafModuli value L R j := by
  induction T generalizing L R with
  | leaf => simp only [realValueLeafModuli, realLeafModuli, realSlotProduct_nat]
  | node s CL CR u left right ihL ihR =>
    cases j with
    | inl j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihL]
    | inr j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihR]

theorem realValueNodeCutoff_nat {σ : Type*} (value : σ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) :
    realValueNodeCutoff (fun i => (value i : ℝ)) φ G T L R = movingRealNodeCutoff value φ G T L R := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [realValueNodeCutoff, movingRealNodeCutoff, MovingSlotReversal.realValuePivot_nat, ihL, ihR]

/-- The extension agrees exactly with the original function at every natural
prime tuple, including points where a cutoff vanishes. -/
theorem realValueSmoothWeight_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueSmoothWeight (fun i => (value i : ℝ)) T ψ X lo hi hlo hhi φ G L R =
      movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G L R := by
  simp only [realValueSmoothWeight, movingRealSmoothWeight, realValueFourierWeight,
    movingRealFourierWeight, realValueNodeCutoff_nat, MovingSlotData.realValueLeafModuli_nat]

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeRestorationDifference
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deletion and collision errors for arbitrary signed prime observables -/

namespace Ostmann
open scoped Classical BigOperators

/-- Monotone restoration costs exactly the excess mass of the product law.
The observable can retain residue classes and every other arithmetic factor. -/
theorem finite_product_restoration_difference {J A : Type*} [Fintype J] [Fintype A]
    (μ ν : J → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (hle : ∀ j a, μ j a ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (F : (J → A) → ℂ)
    (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x, ((∏ j, μ j (x j) : ℝ) : ℂ) * F x) -
      ∑ x, ((∏ j, ν j (x j) : ℝ) : ℂ) * F x‖ ≤
      B * ((∏ j, ∑ a, ν j a) - 1) := by
  have hp (x : J → A) : (∏ j, μ j (x j)) ≤ ∏ j, ν j (x j) :=
    Finset.prod_le_prod (fun j _ => hμ j (x j)) (fun j _ => hle j (x j))
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : J → A, B * ((∏ j, ν j (x j)) - ∏ j, μ j (x j)) := by
      apply norm_sum_le_of_le
      intro x _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hp x))]
      exact (mul_le_mul_of_nonneg_left (hF x) (sub_nonneg.mpr (hp x))).trans_eq
        (mul_comm _ _)
    _ = B * ((∏ j, ∑ a, ν j a) - 1) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib,
        ← Fintype.prod_sum, ← Fintype.prod_sum]
      simp only [hmass, Finset.prod_const_one]

/-- Restoring deleted atoms retains the old normalization. -/
theorem original_prime_restoration_difference {J : Type*} [Fintype J]
    (P : Finset ℕ) (S D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hS : ∀ j, (∑ p ∈ S j \ D j, (p : ℝ)⁻¹) ≠ 0)
    (F : (J → P) → ℂ) (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
    ‖(∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x) -
      ∑ x, ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) * F x‖ ≤
      B * ((∏ j, (1 + Z j * ∑ p ∈ S j ∩ D j, (p : ℝ)⁻¹)) - 1) := by
  dsimp only
  let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
  let ν := fun j (p : P) => if (p : ℕ) ∈ S j then Z j * (p : ℝ)⁻¹ else 0
  have hle (j : J) (p : P) : primeSubsetPrior P (S j \ D j) p ≤ ν j p := by
    by_cases hp : (p : ℕ) ∈ S j \ D j
    · have hps := (Finset.mem_sdiff.mp hp).1
      simp only [primeSubsetPrior, hp, hps, ite_true, if_true, ν, Z, div_eq_mul_inv]
      exact le_of_eq (mul_comm _ _)
    · simp only [primeSubsetPrior, hp, ite_false, if_false]
      dsimp only [ν]
      split_ifs <;> positivity
  have hm (j : J) : (∑ p : P, ν j p) =
      1 + Z j * ∑ p ∈ S j ∩ D j, (p : ℝ)⁻¹ := by
    have he : (∑ p : P, ν j p) = Z j * ∑ p ∈ S j, (p : ℝ)⁻¹ := by
      dsimp only [ν]
      rw [Finset.sum_coe_sort P (fun p : ℕ => if p ∈ S j then Z j * (p : ℝ)⁻¹ else 0)]
      rw [← Finset.sum_filter]
      have hfilter : P.filter (· ∈ S j) = S j := by
        ext p
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun hp => ⟨hSP j hp, hp⟩⟩
      rw [hfilter, Finset.mul_sum]
    rw [he, ← Finset.sum_inter_add_sum_sdiff (S j) (D j) (fun p : ℕ => (p : ℝ)⁻¹), mul_add]
    have hz : Z j * (∑ p ∈ S j \ D j, (p : ℝ)⁻¹) = 1 := inv_mul_cancel₀ (hS j)
    rw [hz, add_comm]
  have h := finite_product_restoration_difference
    (fun j => primeSubsetPrior P (S j \ D j)) ν
    (fun j p => primeSubsetPrior_nonneg P (S j \ D j) p) hle
    (fun j => primeSubsetPrior_mass P (S j \ D j) (Finset.sdiff_subset.trans (hSP j)) (hS j)) F B hF
  simpa only [hm] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkDeletionCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deleted-atom costs in the actual original bulk prior -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulk_deleted_reciprocal_mass_le (S D : Finset ℕ) (T : ℝ)
    (hlow : ∀ q ∈ S, Real.exp T ≤ (q : ℝ)) :
    (∑ q ∈ S ∩ D, (q : ℝ)⁻¹) ≤ (D.card : ℝ) * Real.exp (-T) := by
  calc
    _ ≤ ∑ _q ∈ S ∩ D, Real.exp (-T) := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [Real.exp_neg] using inv_anti₀ (Real.exp_pos T)
        (hlow q (Finset.mem_inter.mp hq).1)
    _ = ((S ∩ D).card : ℝ) * Real.exp (-T) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
      (Real.exp_nonneg _)

/-- All deleted values are charged using the old normalizers. If their
total mass is at most one, the product excess is at most twice that mass. -/
theorem bulk_deleted_product_cost {J : Type*} [Fintype J]
    (S D : J → Finset ℕ) (Z : J → ℝ) (H T K : ℝ)
    (hZ0 : ∀ j, 0 ≤ Z j) (hZ : ∀ j, Z j ≤ Real.exp H)
    (hcard : ∀ j, (D j).card ≤ K)
    (hlow : ∀ j q, q ∈ S j → Real.exp T ≤ (q : ℝ))
    (hsmall : (Fintype.card J : ℝ) * K * Real.exp (H - T) ≤ 1) :
    (∏ j, (1 + Z j * ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1 ≤
      2 * (Fintype.card J : ℝ) * K * Real.exp (H - T) := by
  let x := fun j => Z j * ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹
  have hx0 (j) : 0 ≤ x j := mul_nonneg (hZ0 j) (Finset.sum_nonneg fun _ _ => by positivity)
  have hx (j) : x j ≤ K * Real.exp (H - T) := by
    have hm := bulk_deleted_reciprocal_mass_le (S j) (D j) T (hlow j)
    have hk : 0 ≤ K := (Nat.cast_nonneg _).trans (hcard j)
    calc
      _ ≤ Real.exp H * ((D j).card * Real.exp (-T)) :=
        mul_le_mul (hZ j) hm (Finset.sum_nonneg fun _ _ => by positivity) (Real.exp_nonneg _)
      _ ≤ Real.exp H * (K * Real.exp (-T)) := by gcongr; exact hcard j
      _ = K * Real.exp (H - T) := by rw [Real.exp_sub, Real.exp_neg]; ring
  have hs0 : 0 ≤ ∑ j, x j := Finset.sum_nonneg fun j _ => hx0 j
  have hs : (∑ j, x j) ≤ (Fintype.card J : ℝ) * K * Real.exp (H - T) := by
    calc
      _ ≤ ∑ _j : J, K * Real.exp (H - T) := Finset.sum_le_sum fun j _ => hx j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have he := Real.abs_exp_sub_one_le (show |∑ j, x j| ≤ 1 by
    rw [abs_of_nonneg hs0]; exact hs.trans hsmall)
  have hp := Real.prod_one_add_le_exp_sum Finset.univ hx0
  change (∏ j, (1 + x j)) - 1 ≤ _
  have he' : Real.exp (∑ j, x j) - 1 ≤ 2 * ∑ j, x j := by
    rw [abs_of_nonneg hs0] at he
    exact (le_abs_self _).trans he
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkDeletionRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform decay of the original deletion and collision costs -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

private theorem bulk_auxiliary_prefactor_le (C L a d H B : ℝ)
    (hC : 1 ≤ C) (hL : 1 ≤ L) (ha0 : 0 ≤ a) (hd0 : 0 ≤ d) (_hB0 : 0 ≤ B)
    (ha : a ≤ C * L) (hd : d ≤ Real.exp (C * L)) (hH : H ≤ C * L)
    (hB : B ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L))) :
    B * (a ^ 2 + 2 * a * d) * Real.exp H ≤
      Real.exp (6 * C * L ^ 2 + 6 * C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hae : a ≤ Real.exp (C * L) := ha.trans (by linarith [Real.add_one_le_exp (C * L)])
  have hpoly : a ^ 2 + 2 * a * d ≤ 3 * Real.exp (2 * C * L) := by
    have hsq := pow_le_pow_left₀ ha0 hae 2
    have had := mul_le_mul hae hd hd0 (Real.exp_nonneg _)
    rw [← Real.exp_nat_mul] at hsq
    have hsq' : a ^ 2 ≤ Real.exp (2 * C * L) := by
      convert hsq using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    rw [← Real.exp_add] at had
    have he : C * L + C * L = 2 * C * L := by ring
    rw [he] at had
    nlinarith [hsq']
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  calc
    _ ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        (3 * Real.exp (2 * C * L)) * Real.exp (C * L) := by
      gcongr
    _ ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        (Real.exp 2 * Real.exp (2 * C * L)) * Real.exp (C * L) := by gcongr
    _ ≤ _ := by
      simp only [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hLsq : L ≤ L ^ 2 := by nlinarith
      have hCLsq : 1 ≤ C * L ^ 2 := by nlinarith
      have he : 0 ≤ C * L * Real.exp ((1 / 1000 : ℝ) * L) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hLsq hC0]

/-- The cutoff precedes the bulk dimension, deletion sets, and original
normalizers. Both bad-event costs have a stronger saving than the cell error. -/
theorem bulk_collision_deletion_numerical_rate (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ a d H T B : ℝ,
      0 ≤ a → 0 ≤ d → 0 ≤ B → a ≤ C * L → d ≤ Real.exp (C * L) → H ≤ C * L →
      B ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      a * d * Real.exp (H - T) ≤ Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) ∧
      B * (a ^ 2 + 2 * a * d) * Real.exp (H - T) ≤
        Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  filter_upwards [arithmetic_error_absorption (1 / 1000) (39 / 10000) (2 / 1000)
    (6 * C) 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro a d H T B ha0 hd0 hB0 ha hd hH hB hT
  have hB1 : (1 : ℝ) ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) :=
    Real.one_le_exp_iff.mpr (by
      have : 0 ≤ C := by linarith
      have : 0 ≤ L := by linarith
      positivity)
  have hp := bulk_auxiliary_prefactor_le C L a d H B hC hL ha0 hd0 hB0 ha hd hH hB
  have hp1 := bulk_auxiliary_prefactor_le C L a d H 1 hC hL ha0 hd0 (by norm_num) ha hd hH hB1
  have hmass : a * d * Real.exp H ≤
      Real.exp (6 * C * L ^ 2 + 6 * C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply le_trans _ hp1
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg ha0 hd0]) (Real.exp_nonneg _)
  have he : Real.exp (-T) ≤ Real.exp (-Real.exp ((39 / 10000 : ℝ) * L)) :=
    Real.exp_le_exp.mpr (neg_le_neg hT)
  have hfinish (b : ℝ) (_hb0 : 0 ≤ b)
      (hb : b * Real.exp H ≤ Real.exp
        (6 * C * L ^ 2 + 6 * C * L * Real.exp ((1 / 1000 : ℝ) * L))) :
      b * Real.exp (H - T) ≤ Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
    rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg, ← mul_assoc]
    exact (mul_le_mul hb he (Real.exp_nonneg _) (Real.exp_nonneg _)).trans (by
      simpa only [one_mul, neg_mul] using hrate)
  exact ⟨hfinish (a * d) (mul_nonneg ha0 hd0) hmass,
    hfinish (B * (a ^ 2 + 2 * a * d)) (by positivity) hp⟩

/-- The actual deleted-set expression, with all old normalizers, and the
distinctness error are absorbed together. -/
theorem bulk_collision_deletion_rate (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (J : Type) [Fintype J] (S D : J → Finset ℕ)
      (Z : J → ℝ) (H T K B : ℝ),
      (∀ j, 0 ≤ Z j) → (∀ j, Z j ≤ Real.exp H) →
      (∀ j, ((D j).card : ℝ) ≤ K) → 0 ≤ K → 0 ≤ B →
      (Fintype.card J : ℝ) ≤ C * L → K ≤ Real.exp (C * L) → H ≤ C * L →
      B ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      (∀ j q, q ∈ S j → Real.exp T ≤ (q : ℝ)) →
      B * (Fintype.card J : ℝ) ^ 2 * Real.exp (H - T) +
        B * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) ≤
      Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  filter_upwards [bulk_collision_deletion_numerical_rate C hC] with L hrate
  intro J _ S D Z H T K B hZ0 hZ hcard hK hB0 hJ hKbound hH hB hT hlow
  have hb := hrate (Fintype.card J) K H T B (Nat.cast_nonneg _) hK hB0 hJ hKbound hH hB hT
  have hsmall : (Fintype.card J : ℝ) * K * Real.exp (H - T) ≤ 1 :=
    hb.1.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg _)))
  have hd := bulk_deleted_product_cost S D Z H T K hZ0 hZ hcard hlow hsmall
  apply le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd hB0)) _
  calc
    _ = B * ((Fintype.card J : ℝ) ^ 2 + 2 * (Fintype.card J : ℝ) * K) * Real.exp (H - T) := by ring
    _ ≤ _ := hb.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryRealEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real evaluation of the original cleared history formulas -/

namespace Ostmann.HistoryFormula
open scoped Classical BigOperators

theorem realEval_bind {σ τ : Type*} (F : HistoryFormula σ) (f : σ → HistoryFormula τ)
    (x : τ → ℝ) : (F.bind f).realEval x = F.realEval (fun i => (f i).realEval x) := by
  induction F with
  | prime i => simp only [bind, realEval_prime]
  | external z => simp only [bind, realEval_external]
  | product l r hl hr => simp only [bind, realEval_product, hl, hr]
  | solve l r v w s hs hl hr => simp only [bind, realEval_solve, hl, hr]

theorem realEval_listProduct {σ : Type*} (fs : List (HistoryFormula σ)) (x : σ → ℝ) :
    (listProduct fs).realEval x = (fs.map (fun F => F.realEval x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, realEval_product, List.map_cons, List.prod_cons, ih]

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealNodeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original real node inequalities with variable bulk values -/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.giantFormula_realEval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (hs : s.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value s.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (s.giantFormula value hs hu L R).realEval x =
      s.realValuePivot (fun i => (value i : ℝ)) (L.realEval x) (R.realEval x) := by
  simp only [giantFormula, HistoryFormula.realEval_solve, HistoryFormula.realEval_product,
    HistoryFormula.realEval_external, Int.cast_mul, Int.cast_natCast, realValuePivot,
    realSlotProduct_nat]
  ring

theorem movingNodeGuard_realEval (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).archimedeanAt x ↔
      1 ≤ ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ∧
      ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ≤ pivotBound ∧
      ((2 * pivotBound * childBound + 1 : ℕ) : ℝ) ≤ R.realEval x * CR := by
  simp only [movingNodeGuard, wordTransferGuard, WordTransferGuard.archimedeanAt,
    HistoryFormula.realEval_bind, HistoryPivotStep.formula, wordTransferStep, movingNodeWord,
    HistoryFormula.realEval_solve, HistoryFormula.realEval_listProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, HistoryFormula.realEval_prime, Bool.false_eq_true, ite_false, if_false,
    ite_true, if_true, HistoryFormula.realEval_product, HistoryFormula.realEval_external, Int.cast_natCast, mul_one]
  ring_nf

/-- Exact agreement with all original archimedean formula-node tests. -/
theorem realValueNodeSupport_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    movingArchimedeanGate (T.formulaNodes value hvalue childBound pivotBound hf L R) x ↔
      realValueNodeSupport (fun i => (value i : ℝ)) childBound pivotBound T (L.realEval x) (R.realEval x) := by
  induction T generalizing L R with
  | leaf => simp [MovingSlotData.formulaNodes, movingArchimedeanGate, realValueNodeSupport]
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.formulaNodes, movingArchimedeanGate, List.forall_mem_cons,
      List.forall_mem_append, realValueNodeSupport]
    rw [show (∀ f ∈ left.formulaNodes value hvalue childBound pivotBound hf.2.1
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) L, f.guard.archimedeanAt x) ↔ _ from
      ihL hf.2.1 _ L,
      show (∀ f ∈ right.formulaNodes value hvalue childBound pivotBound hf.2.2
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) R, f.guard.archimedeanAt x) ↔ _ from
      ihR hf.2.2 _ R]
    rw [movingNodeGuard_realEval]
    simp only [MovingSlotReversal.giantFormula_realEval, MovingSlotReversal.realCompositePivot,
      MovingSlotData.step, realSlotProduct_nat]
    tauto

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original kernel on real bulk coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

/-- The real extension has precisely the old arithmetic gates and windows. -/
theorem realValueSupportFlag_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (X lo hi L R : ℝ) :
    realValueSupportFlag (fun i => (value i : ℝ)) childBound pivotBound T X lo hi L R =
      movingRealGateWeight value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        X lo hi (topGiantReal L R) := by
  have hn := realValueNodeSupport_nat value hv childBound pivotBound T hf
    (.prime false) (.prime true) (topGiantReal L R)
  simp only [HistoryFormula.realEval_prime, topGiantReal, Bool.false_eq_true, ite_false, if_false, ite_true, if_true] at hn
  simp only [realValueSupportFlag, realValueFullSupport, movingRealGateWeight,
    movingArchimedeanFlag, movingRealWindowFlag, MovingSlotData.realValueLeafModuli_nat,
    topGiantReal, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  rw [hn]
  split_ifs <;> simp_all

theorem realValueKernel_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernel (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernel value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernel, realValueSupportFlag_nat value hv childBound pivotBound T hf,
    realValueSmoothWeight_nat]
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

theorem centeredDensity_sq_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, centeredDensity S x ^ 2) = (p : ℝ) * residueVariance S := by
  let σ := residueDensity S
  have hsq (x : ZMod p) : centeredDensity S x ^ 2 =
      (if x ∈ S then 1 - 2 * σ else 0) + σ ^ 2 := by
    dsimp [centeredDensity, σ, residueDensity]
    split <;> ring
  simp_rw [hsq]
  rw [Finset.sum_add_distrib]
  have hsum : (∑ x : ZMod p, if x ∈ S then (1 - 2 * σ) else 0) = S.card * (1 - 2 * σ) := by simp; ring
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hσ : (p : ℝ) * σ = S.card := by dsimp [σ, residueDensity]; field_simp
  change _ = (p : ℝ) * (σ * (1 - σ))
  rw [← hσ]
  ring

theorem normalizedResidueIndicator_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, normalizedResidueIndicator S x) = 0 := by
  simp only [normalizedResidueIndicator, ← Complex.ofReal_sum, ← Finset.sum_div,
    centeredDensity_sum, zero_div, Complex.ofReal_zero]

theorem normalizedResidueIndicator_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueIndicator S x‖ ^ 2) = p := by
  have hv := residueVariance_pos S hS hSp
  simp only [normalizedResidueIndicator, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_pow, ← Finset.sum_div, Real.sq_sqrt hv.le, centeredDensity_sq_sum]
  exact mul_div_cancel_right₀ (p : ℝ) hv.ne'

theorem normalizedResidueTransform_zero {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    normalizedResidueTransform S 0 = 0 := by
  simp only [normalizedResidueTransform, densityFourier, additiveFourier_apply,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, normalizedResidueIndicator_sum]

theorem normalizedResidueTransform_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueTransform S x‖ ^ 2) = p := by
  rw [normalizedResidueTransform, densityFourier_energy, normalizedResidueIndicator_energy S hS hSp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original paired kernel as a bounded measurable bulk integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem realValueKernelPair_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernelPair (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernelPair value T
        (fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernelPair, realValueKernel_nat value hv childBound pivotBound (T false) (hf false),
    realValueKernel_nat value hv childBound pivotBound (T true) (hf true)]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingModularSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spectator evaluation without internal primes in the period

At a spectator prime the entire reversal denominator is a unit. The field
recursion therefore depends only on the two spectator residues, even though
the original recursion used integer division by compensation products.
-/

namespace Ostmann
open scoped Classical

theorem movingModularSpectator_norm {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ z, ‖g z‖ ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q) :
    ‖movingModularSpectator value q g D T x y‖ ≤ B ^ (2 ^ n) := by
  induction T generalizing x y with
  | leaf => simpa only [movingModularSpectator, pow_zero, pow_one] using hg _
  | @node n s CL CR U left right ihL ihR =>
    rw [movingModularSpectator]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hB (2 ^ (n + 1))
    · rw [norm_mul, norm_star]
      calc
        _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
          mul_le_mul (ihL _ _) (ihR _ _) (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedAverageNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete norm budgets for the retained arithmetic averages -/

namespace Ostmann
open scoped Classical BigOperators

private theorem finiteMean_norm_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℂ) (B : ℝ) (hf : ∀ a, ‖f a‖ ≤ B) :
    ‖(Fintype.card A : ℂ)⁻¹ * ∑ a, f a‖ ≤ B := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hf a))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem pageGiantWeight_norm_le_two (input : PublishedProgressionInput) (Q q a : ℕ)
    (y : ℝ) (hy : 0 ≤ y) : ‖pageGiantWeight input Q q a y‖ ≤ 2 := by
  have h := pageMultiplier_bounds
    (fun a => pageCoefficient (pageAtModulus q (selectedPageZero input Q)) a)
    (pageBeta (pageAtModulus q (selectedPageZero input Q))) y
    (pageCoefficient_abs_le_one _) (pageBeta_le_one _) hy a
  rw [pageGiantWeight, Complex.norm_real, Real.norm_of_nonneg h.1]
  exact h.2

theorem movingFrequencyPageAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ)
    (y : ℝ) (hy : 0 ≤ y) :
    ‖movingFrequencyPageAverage value outside F E T nodes R r input Q y‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  apply finiteMean_norm_le
  intro z
  have hf : ‖movingFrequencyPairFactor value outside F E T nodes R z.1.val z.2.val.val‖ ≤
      ‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖ := by
    unfold movingFrequencyPairFactor
    split_ifs
    · simp only [norm_mul, Complex.norm_conj, le_refl]
    · exact (norm_zero : ‖(0 : ℂ)‖ = 0) ▸ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [norm_mul]
  calc
    _ ≤ (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) * 2 :=
      mul_le_mul hf (pageGiantWeight_norm_le_two input Q r z.2.val.val y hy)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := mul_comm _ _

theorem movingSpectatorHaarAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ z, ‖g z‖ ≤ B) :
    ‖movingSpectatorHaarAverage value q g D T‖ ≤ B ^ (2 ^ (n + 1)) := by
  apply finiteMean_norm_le
  intro z
  rw [movingSpectatorPairFactor, norm_mul, Complex.norm_conj]
  calc
    _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
      mul_le_mul (movingModularSpectator_norm value q g (D false) B hB hg (T false) z.1 z.2)
        (movingModularSpectator_norm value q g (D true) B hB hg (T true) z.1 z.2)
        (norm_nonneg _) (pow_nonneg hB _)
    _ = _ := by rw [← pow_add, pow_succ]; congr 1; omega

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting the actual cells and residues in the bulk comparison error -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem bulkPrimeErrorFactor_nonneg (P : PublishedProgressionInput) (Q : ℕ) (u : ℝ) :
    0 ≤ bulkPrimeErrorFactor P Q u := by
  unfold bulkPrimeErrorFactor
  have := P.errorConstant_nonneg
  positivity

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

theorem bulkKernelPairComparisonBudget_nonneg (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e : ℕ) (B D : ℝ) : 0 ≤ bulkKernelPairComparisonBudget ψ V lo hi n d r e B D := by
  unfold bulkKernelPairComparisonBudget
  positivity

/-- Every residue and real cell in the actual comparison is counted here;
only the smallest lower endpoint is used for the progression saving. -/
theorem bulk_weighted_error_budget {J Cell : Type*} [Fintype J] [Fintype Cell]
    (P : PublishedProgressionInput) {Q M : ℕ} [NeZero M] (hQ : 2 ≤ Q)
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (a : (J → (ZMod M)ˣ) → ℂ) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ z, ‖a z‖ ≤ A)
    (u : J → Cell → ℝ) (T : ℝ) (hu : ∀ j c, T ≤ u j c)
    (B : ℝ) (hB : 0 ≤ B) :
    (∏ j, Z j) * ∑ c : J → Cell, ∑ z : J → (ZMod M)ˣ, ‖a z‖ *
      (2 ^ Fintype.card J * ∑ j, B * bulkPrimeErrorFactor P Q (u j (c j))) ≤
    ((∏ j, Z j) * (Fintype.card Cell : ℝ) ^ Fintype.card J *
      (Fintype.card (ZMod M)ˣ : ℝ) ^ Fintype.card J * A *
      2 ^ Fintype.card J * (Fintype.card J : ℝ) * B) * bulkPrimeErrorFactor P Q T := by
  have hpoint (c : J → Cell) :
      2 ^ Fintype.card J * ∑ j, B * bulkPrimeErrorFactor P Q (u j (c j)) ≤
      2 ^ Fintype.card J * (Fintype.card J : ℝ) * B * bulkPrimeErrorFactor P Q T := by
    apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (bulkPrimeErrorFactor_antitone P hQ (hu j (c j))) hB) (by positivity))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring_nf
    rfl
  calc
    _ ≤ (∏ j, Z j) * ∑ _c : J → Cell, ∑ _z : J → (ZMod M)ˣ,
        A * (2 ^ Fintype.card J * (Fintype.card J : ℝ) * B * bulkPrimeErrorFactor P Q T) := by
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun j _ => hZ j)
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul (ha z) (hpoint c)
        (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
          mul_nonneg hB (bulkPrimeErrorFactor_nonneg P Q (u j (c j))))) hA
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, nsmul_eq_mul]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RetainedPrimeNormalization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizers after the actual finite prime exclusions -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem retained_prime_mass_lower (S D : Finset ℕ) (a : ℝ) (ha : 0 < a)
    (hmass : a ≤ ∑ p ∈ S, (p : ℝ)⁻¹)
    (hdeleted : (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ a / 2) :
    a / 2 ≤ (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
      0 < (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
      (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ ≤ 2 / a := by
  have hsplit := Finset.sum_inter_add_sum_sdiff S D (fun p : ℕ => (p : ℝ)⁻¹)
  have hlower : a / 2 ≤ ∑ p ∈ S \ D, (p : ℝ)⁻¹ := by linarith
  refine ⟨hlower, lt_of_lt_of_le (by positivity) hlower, ?_⟩
  have hi := inv_anti₀ (show 0 < a / 2 by positivity) hlower
  apply hi.trans_eq
  field_simp

theorem retained_prime_normalizer_rate (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (S D : Finset ℕ) (T : ℝ),
      Real.exp (-C * L) ≤ (∑ p ∈ S, (p : ℝ)⁻¹) →
      (D.card : ℝ) ≤ Real.exp (C * L) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      (∀ p ∈ S, Real.exp T ≤ (p : ℝ)) →
      0 < (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
        (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp ((C + 1) * L) := by
  filter_upwards [arithmetic_exponent_absorption 0 (39 / 10000) 0 (2 * C) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro S D T hmass hcard hT hlow
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hsmall : 2 * C * L - T ≤ -1 := by
    simp only [zero_mul, Real.exp_zero, mul_one, pow_one] at hrate
    nlinarith [mul_nonneg hC0 hL0]
  have he : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) htwo
  have hdel : (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ Real.exp (-C * L) / 2 := by
    calc
      _ ≤ (D.card : ℝ) * Real.exp (-T) := bulk_deleted_reciprocal_mass_le S D T hlow
      _ ≤ Real.exp (C * L) * Real.exp (-T) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (-C * L) * Real.exp (2 * C * L - T) := by
        simp only [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-C * L) * (1 / 2) :=
        mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr hsmall).trans he) (Real.exp_nonneg _)
      _ = _ := by ring
  have hm := retained_prime_mass_lower S D (Real.exp (-C * L)) (Real.exp_pos _) hmass hdel
  refine ⟨hm.2.1, hm.2.2.trans ?_⟩
  have htwo : (2 : ℝ) ≤ Real.exp L := by
    apply le_trans _ (Real.exp_le_exp.mpr hL)
    linarith [Real.add_one_le_exp 1]
  calc
    2 / Real.exp (-C * L) = 2 * Real.exp (C * L) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ ≤ Real.exp L * Real.exp (C * L) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp ((C + 1) * L) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalHarmonicMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real box mass with the deleted-prime normalizer -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem PublishedProgressionInput.primeCellSupport_harmonic_error
    (P : PublishedProgressionInput) {C : Type*} [Fintype C]
    (Q : ℕ) (hQ : 2 ≤ Q) (u v : C → ℝ)
    (hu : ∀ c, 1 ≤ u c) (huv : ∀ c, u c ≤ v c) (hshort : ∀ c, v c ≤ u c + 1)
    (hsep : ∀ c d, c ≠ d → v c ≤ u d ∨ v d ≤ u c) :
    |(∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v, (p : ℝ)⁻¹) -
      ∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹| ≤
        ∑ c, bulkPrimeErrorFactor P Q (u c) := by
  have hs : (∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v, (p : ℝ)⁻¹) =
      ∑ c, ∑ p ∈ primeLogCellSet 1 0 (u c) (v c), (p : ℝ)⁻¹ := by
    unfold primeCellSupport
    rw [Finset.sum_biUnion]
    intro c _ d _ hcd
    exact primeLogCellSet_disjoint 1 0 0 (u c) (v c) (u d) (v d) (Or.inr (hsep c d hcd))
  rw [hs, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro c _
  have he := primeLogCell_page_mass_error P hQ (by norm_num : 1 ≤ (1 : ℕ))
    (by omega : 1 ≤ Q) (by simp : Nat.Coprime 0 1) (u c) (v c) (hu c) (huv c) (hshort c)
  rw [primeLogCellMeasure_mass,
    primeGiantMeasure_one_mass P Q 0 (u c) (v c) (by linarith [hu c])] at he
  exact he

/-- Deleting a small amount of original prime mass does not invalidate
the required bound on the normalized real box mass. -/
theorem deleted_harmonic_mass_le_two (S D : Finset ℕ) (a I err : ℝ)
    (ha : 0 < a) (hmass : a ≤ ∑ p ∈ S, (p : ℝ)⁻¹)
    (hdeleted : (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ a / 4)
    (herror : |(∑ p ∈ S, (p : ℝ)⁻¹) - I| ≤ err) (herr : err ≤ a / 4) :
    0 < (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
      (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ * I ≤ 2 := by
  have hs := Finset.sum_inter_add_sum_sdiff S D (fun p : ℕ => (p : ℝ)⁻¹)
  have hp : 0 < ∑ p ∈ S \ D, (p : ℝ)⁻¹ := by linarith
  refine ⟨hp, ?_⟩
  rw [mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ hp).mpr
  have he := (abs_le.mp herror).1
  linarith

theorem PublishedProgressionInput.original_harmonic_box_mass
    (P : PublishedProgressionInput) {C : Type*} [Fintype C]
    (Q : ℕ) (hQ : 2 ≤ Q) (u v : C → ℝ)
    (hu : ∀ c, 1 ≤ u c) (huv : ∀ c, u c ≤ v c) (hshort : ∀ c, v c ≤ u c + 1)
    (hsep : ∀ c d, c ≠ d → v c ≤ u d ∨ v d ≤ u c)
    (D : Finset ℕ) (a : ℝ) (ha : 0 < a)
    (hmass : a ≤ ∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v, (p : ℝ)⁻¹)
    (hdeleted : (∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v ∩ D, (p : ℝ)⁻¹) ≤ a / 4)
    (herror : (∑ c, bulkPrimeErrorFactor P Q (u c)) ≤ a / 4) :
    (∑ p ∈ primeCellSupport 1 (fun _ : C => 0) u v \ D, (p : ℝ)⁻¹)⁻¹ *
      (∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹) ≤ 2 :=
  (deleted_harmonic_mass_le_two _ D a _ _ ha hmass hdeleted
    (P.primeCellSupport_harmonic_error Q hQ u v hu huv hshort hsep) herror).2

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkHalfLogBudgetComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cost of retaining the original terminal logarithmic factors -/

namespace Ostmann
open scoped SchwartzMap

/-- Two half-bulk factors per leaf in each tree fit the existing derivative-root budget. -/
theorem bulkHalfLogWeightedKernelPairBudget_le
    (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ) (n d r e t rlog : ℕ) (B D Dlog : ℝ)
    (hDlog : 0 ≤ Dlog) (ht : t ≤ 4 * 2 ^ n) (hr : rlog ≤ r) :
    bulkLogWeightedKernelPairBudget ψ V lo hi n d r e t rlog B D Dlog ≤
      (2 * (2 + Dlog * (Real.exp 2 - 1)) ^ t) *
        bulkKernelPairComparisonBudget ψ V lo hi n d r e B D := by
  let H := 2 * (n * d + e) + r
  let A := (2 ^ n + (2 ^ n - 1)) * H
  let B' := (3 * (2 ^ n - 1) + 2 * 2 ^ n) * H
  have htr : t * rlog ≤ 2 * B' := by
    calc
      _ ≤ (4 * 2 ^ n) * r := Nat.mul_le_mul ht hr
      _ = 2 * ((2 * 2 ^ n) * r) := by ring
      _ ≤ 2 * B' := Nat.mul_le_mul_left 2
        (Nat.mul_le_mul (by omega)
          (show r ≤ H by dsimp only [H]; omega))
  have hcount : 2 * (A + B') + t * rlog + 1 ≤ 2 * (2 * (A + B') + 1) := by omega
  have hcountR : ((2 * (A + B') + t * rlog + 1 : ℕ) : ℝ) ≤
      2 * ((2 * (A + B') + 1 : ℕ) : ℝ) := by exact_mod_cast hcount
  have hexp : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hfactor : 0 ≤ (2 + Dlog * (Real.exp 2 - 1)) ^ t :=
    pow_nonneg (add_nonneg (by norm_num) (mul_nonneg hDlog hexp)) _
  have h := mul_le_mul_of_nonneg_right hcountR
    (mul_nonneg (sq_nonneg
      (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1))) hfactor)
  change ((2 * (A + B') + t * rlog + 1 : ℕ) : ℝ) *
      ((movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 *
        (2 + Dlog * (Real.exp 2 - 1)) ^ t) ≤ _
  exact h.trans_eq (by dsimp only [bulkKernelPairComparisonBudget, A, B', H]; ring)

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

theorem spectatorBulkCount_upper (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L := by
  have h := Nat.floor_le (show 0 ≤ (k : ℝ) ^ 4 * L / 2 by positivity)
  unfold spectatorBulkCount
  push_cast
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkWeightedCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full bulk cell and residue count fits the progression budget -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulk_weighted_cost_le_exp {J Cell : Type*} [Fintype J] [Fintype Cell]
    (M : ℕ) [NeZero M] (Z : J → ℝ) (A B C L : ℝ)
    (hC : 1 ≤ C) (hL : 1 ≤ L) (hZ0 : ∀ j, 0 ≤ Z j) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hJ : (Fintype.card J : ℝ) ≤ C * L) (hZ : ∀ j, Z j ≤ Real.exp (C * L))
    (hcell : (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)))
    (hunit : (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)))
    (hA : A ≤ Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)))
    (hB : B ≤ Real.exp (C * L ^ 2)) :
    (∏ j, Z j) * (Fintype.card Cell : ℝ) ^ Fintype.card J *
        (Fintype.card (ZMod M)ˣ : ℝ) ^ Fintype.card J * A *
        2 ^ Fintype.card J * (Fintype.card J : ℝ) * B ≤
      Real.exp (8 * C ^ 2 * L ^ 2 + 8 * C ^ 2 * L * Real.exp ((14 / 10000 : ℝ) * L)) := by
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hCL : 0 ≤ C * L := mul_nonneg hC0 hL0
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hCeq : C ≤ C ^ 2 := by nlinarith
  have hbig : Real.exp ((12 / 10000 : ℝ) * L) ≤ Real.exp ((14 / 10000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsmall : Real.exp ((1 / 1000 : ℝ) * L) ≤ Real.exp ((14 / 10000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hz : (∏ j, Z j) ≤ Real.exp (C ^ 2 * L ^ 2) := by
    calc
      _ ≤ ∏ _j : J, Real.exp (C * L) := Finset.prod_le_prod (fun j _ => hZ0 j) (fun j _ => hZ j)
      _ = Real.exp ((Fintype.card J : ℝ) * (C * L)) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hJ hCL])
  have hp (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L))) :
      x ^ Fintype.card J ≤ Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) := by
    apply (pow_le_pow_left₀ hx0 hx _).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hJ (Real.exp_nonneg _))
  have hc := hp _ (Nat.cast_nonneg _) hcell
  have hu := hp _ (Nat.cast_nonneg _) (hunit.trans (Real.exp_le_exp.mpr hbig))
  have ha : A ≤ Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) :=
    hA.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsmall hCL))
  have htwo : (2 : ℝ) ^ Fintype.card J ≤ Real.exp (C * L ^ 2) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    apply (pow_le_pow_left₀ (by norm_num) he _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hLsq hC0]
  have hj : (Fintype.card J : ℝ) ≤ Real.exp (C * L ^ 2) := by
    apply hJ.trans
    have he := Real.add_one_le_exp (C * L)
    exact (by linarith : C * L ≤ Real.exp (C * L)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLsq hC0))
  calc
    _ ≤ Real.exp (C ^ 2 * L ^ 2) *
        Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        Real.exp (C * L ^ 2) * Real.exp (C * L ^ 2) * Real.exp (C * L ^ 2) := by
      gcongr
    _ ≤ _ := by
      simp only [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h₁ := mul_le_mul_of_nonneg_right
        (show C ^ 2 + 3 * C ≤ 8 * C ^ 2 by nlinarith) (sq_nonneg L)
      have h₂ := mul_le_mul_of_nonneg_right
        (show 3 * C ≤ 8 * C ^ 2 by nlinarith) (mul_nonneg hL0 (Real.exp_nonneg ((14 / 10000 : ℝ) * L)))
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkWeightedErrorRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform decay of the full weighted bulk replacement error -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The cutoff is chosen before the finite cell sets, modulus and original
normalizers. Their literal bounds include every joint box and residue. -/
theorem PublishedProgressionInput.bulk_weighted_error_rate
    (P : PublishedProgressionInput) (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (J Cell : Type) [Fintype J] [Fintype Cell]
      (M Q : ℕ) [NeZero M], 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      ∀ (Z : J → ℝ) (a : (J → (ZMod M)ˣ) → ℂ) (A B T : ℝ),
      (∀ j, 0 ≤ Z j) → 0 ≤ A → 0 ≤ B →
      (Fintype.card J : ℝ) ≤ C * L →
      (∀ j, Z j ≤ Real.exp (C * L)) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) →
      A ≤ Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) →
      B ≤ Real.exp (C * L ^ 2) →
      (∀ z, ‖a z‖ ≤ A) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      ∀ u : J → Cell → ℝ, (∀ j c, T ≤ u j c) →
      (∏ j, Z j) * ∑ c : J → Cell, ∑ z : J → (ZMod M)ˣ, ‖a z‖ *
        (2 ^ Fintype.card J * ∑ j, B * bulkPrimeErrorFactor P Q (u j (c j))) ≤
      Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
  filter_upwards [P.bulk_full_progression_budget_rate (8 * C ^ 2) 2,
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro J Cell _ _ M Q _ hQ hlog Z a A B T hZ0 hA0 hB0 hJ hZ hcell hunit hA hB ha hT u hu
  let V := (∏ j, Z j) * (Fintype.card Cell : ℝ) ^ Fintype.card J *
    (Fintype.card (ZMod M)ˣ : ℝ) ^ Fintype.card J * A *
      2 ^ Fintype.card J * (Fintype.card J : ℝ) * B
  have hV : V ≤ Real.exp (8 * C ^ 2 * L ^ 2 +
      8 * C ^ 2 * L * Real.exp ((14 / 10000 : ℝ) * L)) :=
    bulk_weighted_cost_le_exp M Z A B C L hC hL hZ0 hA0 hB0 hJ hZ hcell hunit hA hB
  exact (bulk_weighted_error_budget P hQ Z hZ0 a A hA0 ha u T hu B hB0).trans
    (hrate Q hQ hlog T V hT hV)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenFrequencyAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency/Page average on the fixed bulk residue representative -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingFrequencyCorePageAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ)
    (y : ℝ) (hy : 0 ≤ y) :
    ‖movingFrequencyCorePageAverage value F E T R r input Q y‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  let B := 2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
    ‖movingDataWeight (F true) (E true) (T true)‖)
  have hb (z : ZMod r × (ZMod r)ˣ) :
      ‖movingFrequencyCore value F E T R z.1.val z.2.val.val *
        pageGiantWeight input Q r z.2.val.val y‖ ≤ B := by
    unfold movingFrequencyCore
    split_ifs
    · rw [norm_mul, norm_mul, Complex.norm_conj]
      exact (mul_le_mul_of_nonneg_left (pageGiantWeight_norm_le_two input Q r _ y hy)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (mul_comm _ _)
    · simpa only [zero_mul, norm_zero] using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hc : (Fintype.card (ZMod r × (ZMod r)ˣ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ZMod r × (ZMod r)ˣ) ≠ 0)
  rw [movingFrequencyCorePageAverage, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card (ZMod r × (ZMod r)ˣ) : ℝ)⁻¹ * ∑ _z : ZMod r × (ZMod r)ˣ, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => hb z))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSpectatorNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem movingFieldGiantAmplitude_norm_le {q : ℕ} [Fact q.Prime]
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (D : (ZMod q)ˣ) {n C : ℕ} (T : MovingGiantTree n C)
    (x y : ZMod q) (z : TreeLeafTuple (ZMod q)ˣ n) :
    ‖movingFieldGiantAmplitude g D T x y z‖ ≤ K ^ (2 ^ n) := by
  induction T generalizing x y with
  | leaf s C =>
    simpa only [movingFieldGiantAmplitude, pow_zero, pow_one] using hg _
  | @node n s CL CR u left right ihL ihR =>
    simp only [movingFieldGiantAmplitude]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hK (2 ^ (n + 1))
    · rw [norm_mul, Complex.norm_conj]
      calc
        _ ≤ K ^ (2 ^ n) * K ^ (2 ^ n) :=
          mul_le_mul (ihL _ _ _) (ihR _ _ _) (norm_nonneg _) (pow_nonneg hK _)
        _ = K ^ (2 ^ (n + 1)) := by
          rw [← pow_add, pow_succ]
          congr 1
          omega

theorem frozenBulkSpectatorPair_norm_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (a : (ZMod q)ˣ × (ZMod q)ˣ) (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) :
    ‖frozenBulkSpectatorPair base n m t small samples D e g a z‖ ≤ K ^ (2 ^ (n + 1)) := by
  rw [frozenBulkSpectatorPair, norm_mul, Complex.norm_conj]
  calc
    _ ≤ K ^ (2 ^ n) * K ^ (2 ^ n) :=
      mul_le_mul (movingFieldGiantAmplitude_norm_le g K hK hg _ _ _ _ _)
        (movingFieldGiantAmplitude_norm_le g K hK hg _ _ _ _ _) (norm_nonneg _) (pow_nonneg hK _)
    _ = K ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

/-- The mixed Haar normalization has norm at most one, so the field bound
survives without a factor depending on the spectator prime. -/
theorem frozenBulkSpectatorHaar_norm_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) :
    ‖frozenBulkSpectatorHaar base n m t small samples D e g z‖ ≤ K ^ (2 ^ (n + 1)) := by
  let A := (ZMod q)ˣ × (ZMod q)ˣ
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ha : ‖(Fintype.card A : ℂ)⁻¹ * ∑ a : A,
      frozenBulkSpectatorPair base n m t small samples D e g a z‖ ≤ K ^ (2 ^ (n + 1)) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, K ^ (2 ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
          frozenBulkSpectatorPair_norm_le base n m t small samples D e g K hK hg a z))
          (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = K ^ (2 ^ (n + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hr : ‖(Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_one (by exact_mod_cast (Fact.out : q.Prime).pos)).mpr
    exact_mod_cast (ZMod.card_units q ▸ Nat.sub_le q 1)
  rw [frozenBulkSpectatorHaar, norm_mul]
  exact (mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (pow_nonneg hK (2 ^ (n + 1))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSupportedArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem frozenBulkFrequencyFactor_norm_le {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput)
    (Q : ℕ) (y : ℝ) (hy : 0 ≤ y) (a : J → (ZMod r)ˣ) :
    ‖frozenBulkFrequencyFactor base slot outside F E T childBound R r input Q y a‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  unfold frozenBulkFrequencyFactor
  split_ifs
  · rw [one_mul]
    exact movingFrequencyCorePageAverage_norm_le _ F E T R r input Q y hy
  · rw [zero_mul, norm_zero]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth cost of the actual sharp pattern kernel -/

namespace Ostmann
open scoped SchwartzMap

theorem movingFourierVariationBudget_nonneg (ψ : 𝓢(ℝ, ℂ))
    (V lo hi : ℝ) (n : ℕ) (hV : 0 ≤ V) (hhi : lo ≤ hi) :
    0 ≤ movingFourierVariationBudget ψ V lo hi n := by
  have hB := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD := schwartz_profile_lip_nonneg ψ
  have hW := sub_nonneg.mpr hhi
  unfold movingFourierVariationBudget
  positivity

theorem movingPatternKernelBudget_exp_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A H B D : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) →
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hV⟩ := movingFourierVariationBudget_exp_window ψ n A H hA hH
  let c := (2 ^ n + (2 ^ n - 1)) + (3 * (2 ^ n - 1) + 2 * 2 ^ n)
  let a := 2 * c * (2 * n + 1) * 2 ^ n
  let b := 2 * c * (2 * n * (2 ^ n * (r₀ + 4 * n + 4)) +
    2 ^ n * (r₀ + 4 * n)) + 1
  let K : ℝ := a + b
  let H : ℝ := ((2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hK : 0 < K := by dsimp only [K, b]; positivity
  have hH : 0 ≤ H := sq_nonneg _
  refine ⟨K + 2 * C + H, by positivity, ?_⟩
  intro m lo hi hhi hwidth
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hcount :
      2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n))) +
        ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n)))) + 1 = a * m + b := by
    dsimp only [a, b, c]
    ring
  have hroot : ((a * m + b : ℕ) : ℝ) ≤ Real.exp (K * ((m : ℝ) + 1)) := by
    have hab : ((a * m + b : ℕ) : ℝ) ≤ K * ((m : ℝ) + 1) := by
      push_cast
      dsimp only [K]
      nlinarith [mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) hm]
    exact hab.trans (by linarith [Real.add_one_le_exp (K * ((m : ℝ) + 1))])
  have hv0 := movingFourierVariationBudget_nonneg ψ (Real.exp (A * m)) lo hi n
    (Real.exp_nonneg _) hhi
  have hv2 := pow_le_pow_left₀ hv0 (hV m hm lo hi hhi hwidth) 2
  have hh : H ≤ Real.exp (H * ((m : ℝ) + 1)) := by
    have : H ≤ H * ((m : ℝ) + 1) := by nlinarith [mul_nonneg hH hm]
    exact this.trans (by linarith [Real.add_one_le_exp (H * ((m : ℝ) + 1))])
  unfold bulkKernelPairComparisonBudget
  rw [hcount, mul_pow]
  change ((a * m + b : ℕ) : ℝ) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ^ 2 * H) ≤ _
  calc
    _ ≤ Real.exp (K * ((m : ℝ) + 1)) *
        ((Real.exp (C * ((m : ℝ) + 1))) ^ 2 * Real.exp (H * ((m : ℝ) + 1))) := by
      gcongr
    _ = Real.exp ((K + 2 * C + H) * ((m : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem movingPatternKernelBudget_spectatorScale_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H B D : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * L ^ 2) := by
  obtain ⟨C, hC, hb⟩ := movingPatternKernelBudget_exp_window ψ n r₀ A H B D hA hH
  refine ⟨C * ((k : ℝ) ^ 4 + 1) + 1, ?_, ?_⟩
  · have : 0 ≤ C * ((k : ℝ) ^ 4 + 1) := by positivity
    linarith
  intro L hL
  dsimp only
  intro lo hi hhi hwidth
  apply (hb _ lo hi hhi hwidth).trans
  apply Real.exp_le_exp.mpr
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_upper k L hL0
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hscale : (spectatorBulkCount k L : ℝ) + 1 ≤ ((k : ℝ) ^ 4 + 1) * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hLsq (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)
    nlinarith
  have := mul_le_mul_of_nonneg_left hscale hC.le
  nlinarith [sq_nonneg L]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelGain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quartet gain absorbs the actual sharp-kernel main term -/

namespace Ostmann
open scoped SchwartzMap

theorem bulkKernelPair_smooth_le_budget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e : ℕ) (B D : ℝ) :
    (movingFourierVariationBudget ψ V lo hi n *
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
    bulkKernelPairComparisonBudget ψ V lo hi n d r e B D := by
  let c := 2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)) +
    ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r)))
  have hc : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 c
  exact le_mul_of_one_le_left (sq_nonneg _) hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSpectatorCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise cost of the actual normalized spectator transforms -/

namespace Ostmann
open scoped Classical BigOperators

theorem normalizedResidueTransform_norm_le_sqrt {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    ‖normalizedResidueTransform S x‖ ≤ Real.sqrt (p : ℝ) := by
  have hx : ‖normalizedResidueTransform S x‖ ^ 2 ≤
      ∑ y : ZMod p, ‖normalizedResidueTransform S y‖ ^ 2 :=
    Finset.single_le_sum (f := fun y : ZMod p => ‖normalizedResidueTransform S y‖ ^ 2)
      (fun y _ => sq_nonneg _) (Finset.mem_univ x)
  rw [normalizedResidueTransform_energy S hS hSp] at hx
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p),
    Real.sqrt_nonneg (p : ℝ), norm_nonneg (normalizedResidueTransform S x)]

theorem normalizedResidueTransform_norm_le_prime {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    ‖normalizedResidueTransform S x‖ ≤ p := by
  apply (normalizedResidueTransform_norm_le_sqrt S hS hSp x).trans
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p), Real.sqrt_nonneg (p : ℝ)]

/-- A common prime upper bound controls all actual pointwise spectator
factors. This cost is retained in the cell error, separate from signed gain. -/
theorem moving_spectator_product_cost (n m : ℕ) (p : Fin m → ℕ)
    (V : ℝ) (hp : ∀ i, (p i : ℝ) ≤ Real.exp V) :
    (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp ((2 ^ (n + 1) : ℕ) * (m : ℝ) * V) := by
  calc
    _ ≤ ∏ _i : Fin m, (Real.exp V) ^ (2 ^ (n + 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hp i) _
    _ = _ := by
      simp only [← Real.exp_nat_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      ring

theorem moving_spectator_linear_cost (n m : ℕ) (p : Fin m → ℕ)
    (K L A : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (_hA : 0 ≤ A)
    (hm : (m : ℝ) ≤ K * L) (hamp : A ≤ Real.exp (K * L))
    (hp : ∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) :
    A * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K * L *
        Real.exp ((1 / 1000 : ℝ) * L)) := by
  have hE : 1 ≤ Real.exp ((1 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by positivity)
  calc
    _ ≤ Real.exp (K * L) *
        Real.exp ((2 ^ (n + 1) : ℕ) * (m : ℝ) * Real.exp ((1 / 1000 : ℝ) * L)) :=
      mul_le_mul hamp (moving_spectator_product_cost n m p _ hp)
        (Finset.prod_nonneg fun i _ => by positivity) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (2 ^ (n + 1))))
        (Real.exp_nonneg ((1 / 1000 : ℝ) * L))
      have hKL := mul_le_mul_of_nonneg_left hE (mul_nonneg hK hL)
      nlinarith

theorem moving_frozen_residue_coefficient_norm {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (n m : ℕ) (data : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (P : PublishedProgressionInput) (Q : ℕ)
    (y : ℝ) (hy : 0 ≤ y) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (hSp : ∀ i, (S i).card < p i)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (samples : Bool → MovingSampleSlots σ n)
    (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (a : J → (ZMod r)ˣ) (z : ∀ i, TreeLeafIndex n × Fin m → (ZMod (p i))ˣ) :
    ‖frozenBulkFrequencyFactor base slot outside F E data childBound R r P Q y a *
      ∏ i, frozenBulkSpectatorHaar base n m t small samples (twist i) perm
        (normalizedResidueTransform (S i)) (z i)‖ ≤
      (2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
        ‖movingDataWeight (F true) (E true) (data true)‖)) *
          ∏ i, (p i : ℝ) ^ (2 ^ (n + 1)) := by
  rw [norm_mul, norm_prod]
  apply mul_le_mul
    (frozenBulkFrequencyFactor_norm_le base slot outside F E data childBound R r P Q y hy a)
    (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ =>
      frozenBulkSpectatorHaar_norm_le base n m t small samples (twist i) perm
        (normalizedResidueTransform (S i)) (p i) (Nat.cast_nonneg _)
        (normalizedResidueTransform_norm_le_prime (S i) (hS i) (hSp i)) (z i)))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBadEventRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision and deletion errors for the actual pattern kernel -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

/-- Collision and deletion errors uniformly over the moving Fourier window. -/
theorem movingPattern_bad_event_rate_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H B D F Cnorm : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      ∀ (p : Fin m → ℕ) (S deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (Z : (TreeLeafIndex n × Fin m) → ℝ) (amp H T : ℝ),
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ j, 0 ≤ Z j) → (∀ j, Z j ≤ Real.exp H) →
      (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cnorm * L)) → H ≤ Cnorm * L →
      0 ≤ amp → amp ≤ Real.exp (F * m) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      (∀ j q, q ∈ S j → Real.exp T ≤ (q : ℝ)) →
      let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      let cost := amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) * W
      cost * (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 * Real.exp (H - T) +
        cost * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) ≤
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨Cw, hCw, hkernel⟩ := movingPatternKernelBudget_spectatorScale_window ψ n r₀ k
    A H B D hA hH
  let K := (F + 1) * ((k : ℝ) ^ 4 + 1)
  let C := max (max Cnorm Cw)
    (max ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K) (((2 ^ n : ℕ) : ℝ) * (k : ℝ) ^ 4))
  have hCwC : Cw ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC : 1 ≤ C := hCw.trans hCwC
  have hCn : Cnorm ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCs : (((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCd : ((2 ^ n : ℕ) : ℝ) * (k : ℝ) ^ 4 ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  filter_upwards [bulk_collision_deletion_rate C hC, eventually_ge_atTop (1 : ℝ)] with L hrate hL
  dsimp only
  intro lo hi hhi hwidth p S deleted Z amp H T hp hZ0 hZ hdel hH hamp0 hamp hT hlow
  let m := spectatorBulkCount k L
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  let cost := amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) * W
  have hL0 : 0 ≤ L := by linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hFk : F * (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  have hkK : (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [mul_nonneg hF (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)]
  have hm := spectatorBulkCount_upper k L hL0
  have hmK : (m : ℝ) ≤ K * L := hm.trans (mul_le_mul_of_nonneg_right hkK hL0)
  have hampK : amp ≤ Real.exp (K * L) := hamp.trans (Real.exp_le_exp.mpr (by
    exact (mul_le_mul_of_nonneg_left hm hF).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hFk hL0])))
  have hspec := moving_spectator_linear_cost n m p K L amp hK hL0 hamp0 hmK hampK hp
  have hspec' : amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply hspec.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs hL0) (Real.exp_nonneg _)
  have hW : W ≤ Real.exp (C * L ^ 2) := by
    apply (bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
    exact (hkernel L hL lo hi hhi hwidth).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hCwC (sq_nonneg L)))
  have hcost0 : 0 ≤ cost := by dsimp only [cost, W]; positivity
  have hcost : cost ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply (mul_le_mul hspec' hW (sq_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, add_comm]
  have hdim : (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ≤ C * L := by
    simp only [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCd hL0)
  have hCnL := mul_le_mul_of_nonneg_right hCn hL0
  exact hrate (TreeLeafIndex n × Fin m) S deleted Z H T (Real.exp (Cnorm * L)) cost
    hZ0 hZ hdel (Real.exp_nonneg _) hcost0 hdim
    (Real.exp_le_exp.mpr hCnL) (hH.trans hCnL) hcost hT hlow

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternHalfLogKernelCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth cost of the terminal logarithmic cutoffs -/

namespace Ostmann
open scoped SchwartzMap

/-- Retaining all terminal log weights preserves the quadratic budget,
uniformly in their centers and in the moving Fourier window. -/
theorem movingPatternHalfLogKernelBudget_spectatorScale_window
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (A H B D Dlog : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hDlog : 0 ≤ Dlog) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      ∀ t rlog : ℕ, t ≤ 4 * 2 ^ n → rlog ≤ 2 ^ n * (r₀ + m + 4 * n) →
      bulkLogWeightedKernelPairBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 t rlog B D Dlog ≤
      Real.exp (C * L ^ 2) := by
  obtain ⟨C₀, hC₀, hb⟩ :=
    movingPatternKernelBudget_spectatorScale_window ψ n r₀ k A H B D hA hH
  let a := 2 + Dlog * (Real.exp 2 - 1)
  let K := 2 * a ^ (4 * 2 ^ n)
  have ha : 1 ≤ a := by
    have he : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
    dsimp only [a]
    nlinarith [mul_nonneg hDlog he]
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨C₀ + K, by linarith, ?_⟩
  intro L hL
  dsimp only
  intro lo hi hhi hwindow t rlog ht hrlog
  have hbudget := bulkHalfLogWeightedKernelPairBudget_le ψ (Real.exp (A * spectatorBulkCount k L))
    lo hi n (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n + 4))
    (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n)) 0 t rlog B D Dlog hDlog ht hrlog
  have hfactor : 2 * a ^ t ≤ K :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha ht) (by norm_num)
  have hbase := bulkKernelPairComparisonBudget_nonneg ψ
    (Real.exp (A * spectatorBulkCount k L)) lo hi n
    (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n + 4))
    (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n)) 0 B D
  apply hbudget.trans
  calc
    _ ≤ K * Real.exp (C₀ * L ^ 2) := mul_le_mul hfactor (hb L hL lo hi hhi hwindow) hbase hK
    _ ≤ Real.exp K * Real.exp (C₀ * L ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp K]) (Real.exp_nonneg _)
    _ = Real.exp (K + C₀ * L ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((C₀ + K) * L ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hsq : 1 ≤ L ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq hK]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternHalfLogCellError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cell error with terminal log cutoffs retained -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

/-- The cell threshold is uniform over the moving Fourier window. -/
theorem PublishedProgressionInput.movingPattern_half_log_cell_error_rate_window
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H B D F Cnorm Dlog : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hDlog : 0 ≤ Dlog) (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ n) :
    ∃ C : ℝ, 1 ≤ C ∧ Cnorm ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      ∀ (Cell : Type) [Fintype Cell] (M Q : ℕ) [NeZero M], 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      ∀ (p : Fin m → ℕ) (Z : (TreeLeafIndex n × Fin m) → ℝ)
        (a : ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) → ℂ) (amp T : ℝ) (rlog : ℕ),
      rlog ≤ 2 ^ n * (r₀ + m + 4 * n) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ j, 0 ≤ Z j) → (∀ j, Z j ≤ Real.exp (C * L)) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) →
      0 ≤ amp → amp ≤ Real.exp (F * m) →
      (∀ z, ‖a z‖ ≤ amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      ∀ u : (TreeLeafIndex n × Fin m) → Cell → ℝ, (∀ j c, T ≤ u j c) →
      (∏ j, Z j) * ∑ c : (TreeLeafIndex n × Fin m) → Cell,
        ∑ z : (TreeLeafIndex n × Fin m) → (ZMod M)ˣ, ‖a z‖ *
          (2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ j,
            bulkLogWeightedKernelPairBudget ψ (Real.exp (A * m)) lo hi n
              (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 tlog rlog B D Dlog *
              bulkPrimeErrorFactor P Q (u j (c j))) ≤
        Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
  obtain ⟨C₀, hC₀, hkernel⟩ := movingPatternHalfLogKernelBudget_spectatorScale_window ψ n r₀ k A H B D Dlog hA hH hDlog
  let K := (F + 1) * ((k : ℝ) ^ 4 + 1)
  let C := max C₀ ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K)
    -- The dimension is also charged in the same constant.
  let C' := max (max C (((2 ^ n : ℕ) : ℝ) * (k : ℝ) ^ 4)) Cnorm
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC₀C : C₀ ≤ C' := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hC' : 1 ≤ C' := hC₀.trans hC₀C
  refine ⟨C', hC', le_max_right _ _, ?_⟩
  filter_upwards [P.bulk_weighted_error_rate C' hC', eventually_ge_atTop (1 : ℝ)] with L hrate hL
  dsimp only
  intro lo hi hhi hwidth Cell _ M Q _ hQ hQlog p Z a amp T rlog hrlog hp hZ0 hZ hcell hunit hamp0 hamp ha hT u hu
  let m := spectatorBulkCount k L
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_upper k L hL0
  have hFK : F * (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  have hKk : (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [mul_nonneg hF (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)]
  have hmK : (m : ℝ) ≤ K * L := hm.trans (mul_le_mul_of_nonneg_right hKk hL0)
  have hampK : amp ≤ Real.exp (K * L) := hamp.trans (Real.exp_le_exp.mpr (by
    exact (mul_le_mul_of_nonneg_left hm hF).trans (by nlinarith [mul_le_mul_of_nonneg_right hFK hL0])))
  let bound := amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))
  have hbound0 : 0 ≤ bound := mul_nonneg hamp0 (Finset.prod_nonneg fun i _ => by positivity)
  have hbound : bound ≤ Real.exp (C' * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply (moving_spectator_linear_cost n m p K L amp hK hL0 hamp0 hmK hampK hp).trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hL0
    exact (le_max_right C₀ _).trans ((le_max_left C _).trans (le_max_left _ _))
  have hdim : (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ≤ C' * L := by
    simp only [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ (2 ^ n : ℕ) * ((k : ℝ) ^ 4 * L) :=
        mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
      _ ≤ C' * L := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hL0
  have hbudget := hkernel L hL lo hi hhi hwidth tlog rlog htlog hrlog
  have hbudget' : bulkLogWeightedKernelPairBudget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 tlog rlog B D Dlog ≤
      Real.exp (C' * L ^ 2) :=
    hbudget.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC₀C (sq_nonneg L)))
  have hb := @hrate (TreeLeafIndex n × Fin m) Cell inferInstance inferInstance M Q
    inferInstance hQ hQlog Z a bound
    (bulkLogWeightedKernelPairBudget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 tlog rlog B D Dlog)
    T hZ0 hbound0 (by
      have he : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
      unfold bulkLogWeightedKernelPairBudget
      positivity)
    hdim hZ hcell hunit hbound hbudget' ha hT u hu
  simpa only [finite_univ_canonical] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit size of the actual sharp bulk kernel -/

namespace Ostmann
open scoped Classical SchwartzMap

/-- The bound used in prime replacement is explicit, rather than an
unspecified boundedness constant of the constructed integrand. -/
theorem realValueKernelPair_norm_le {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hcomp : ∀ b, (T b).CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  have hb (b) := realValueKernel_norm value i childBound pivotBound (T b) (hcomp b)
    ψ X lo hi V hlo hhi (hV b) φ G B D hB hD hφ hlip hout L R
  have hpos := (norm_nonneg _).trans (hb false)
  rw [realValueKernelPair, norm_mul, Complex.norm_conj, pow_two]
  exact mul_le_mul (hb false) (hb true) (norm_nonneg _) hpos

theorem movingPattern_kernel_norm_le {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (value : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound
      (movingPatternFinBulkData e n m t small slot perm pattern) ψ X lo hi hlo hhi φ G L R‖ ≤
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 :=
  realValueKernelPair_norm_le value (movingPatternBulkEmbedding e slot j₀) childBound pivotBound _
    (fun b => movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier b j₀)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_UnitPrimeCellSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All unit residues preserve the original selected prime cells -/

namespace Ostmann
open scoped Classical

theorem mem_unitPrimeCellSupport_iff {C : Type*} [Fintype C]
    (q : ℕ) [NeZero q] (u v : C → ℝ) (p : ℕ) :
    p ∈ primeCellSupport q (fun c : C × (ZMod q)ˣ => c.2.val.val)
        (fun c => u c.1) (fun c => v c.1) ↔
      p.Prime ∧ p.Coprime q ∧ ∃ c, Real.log (p : ℝ) ∈ Set.Ioc (u c) (v c) := by
  constructor
  · intro hp
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hprime, hres, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hc
    have heq := (ZMod.natCast_eq_natCast_iff p c.2.val.val q).mpr hres
    simp only [ZMod.natCast_zmod_val] at heq
    have hcop : p.Coprime q := (ZMod.isUnit_iff_coprime p q).mp (by
      rw [heq]
      exact c.2.isUnit)
    exact ⟨hprime, hcop, c.1, hlo, hhi⟩
  · rintro ⟨hprime, hcop, c, hlog⟩
    let z := ZMod.unitOfCoprime p hcop
    apply Finset.mem_biUnion.mpr
    refine ⟨(c, z), Finset.mem_univ _, mem_primeLogCellSet_iff.mpr ⟨hprime, ?_, hlog⟩⟩
    apply (ZMod.natCast_eq_natCast_iff p z.val.val q).mp
    simp [z]

/-- A modulus below every lower endpoint removes no original prime atom. -/
theorem unitPrimeCellSupport_eq {C : Type*} [Fintype C]
    (q : ℕ) [NeZero q] (u v : C → ℝ) (hq : ∀ c, (q : ℝ) ≤ Real.exp (u c)) :
    primeCellSupport q (fun c : C × (ZMod q)ˣ => c.2.val.val)
      (fun c => u c.1) (fun c => v c.1) = primeCellSupport 1 (fun _ : C => 0) u v := by
  ext p
  rw [mem_unitPrimeCellSupport_iff]
  constructor
  · rintro ⟨hp, _, c, hlog⟩
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
      mem_primeLogCellSet_iff.mpr ⟨hp, by simp only [Nat.ModEq, Nat.mod_one], hlog⟩⟩
  · intro hp
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hp, _, hlog⟩ := mem_primeLogCellSet_iff.mp hc
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hqp : q < p := by
      exact_mod_cast (hq c).trans_lt ((Real.lt_log_iff_exp_lt hp0).mp hlog.1)
    exact ⟨hp, hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (NeZero.pos q) hqp), c, hlog⟩

/-- Disjoint real cells and distinct unit residues give the required actual
prime partition, independently of prime-distribution estimates. -/
theorem unitPrimeCells_separated {C : Type*} [Fintype C]
    (q : ℕ) [NeZero q] (u v : C → ℝ)
    (hsep : ∀ c d, c ≠ d → v c ≤ u d ∨ v d ≤ u c) :
    ∀ c d : C × (ZMod q)ˣ, c ≠ d →
      ¬Nat.ModEq q c.2.val.val d.2.val.val ∨ v c.1 ≤ u d.1 ∨ v d.1 ≤ u c.1 := by
  intro c d hcd
  by_cases hfirst : c.1 = d.1
  · left
    intro hres
    apply hcd
    apply Prod.ext hfirst
    apply Units.ext
    have he := (ZMod.natCast_eq_natCast_iff _ _ q).mpr hres
    simpa only [ZMod.natCast_zmod_val] using he
  · exact Or.inr (hsep c.1 d.1 hfirst)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalHarmonicRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The required real box mass under the original deleted prior -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators

theorem deleted_prime_mass_relative_rate (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (S D : Finset ℕ) (T : ℝ),
      (D.card : ℝ) ≤ Real.exp (C * L) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      (∀ p ∈ S, Real.exp T ≤ (p : ℝ)) →
        (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ Real.exp (-C * L) / 4 := by
  filter_upwards [arithmetic_error_absorption 0 (39 / 10000) (2 / 1000) (C + 1) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    double_exp_below_original_mass (2 / 1000) C (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hrelative hL
  intro S D T hD hT hlow
  apply (bulk_deleted_reciprocal_mass_le S D T hlow).trans
  apply le_trans _ (hrate.trans hrelative)
  apply mul_le_mul
  · apply hD.trans
    apply Real.exp_le_exp.mpr
    simp only [pow_one, zero_mul, Real.exp_zero, mul_one]
    have hL0 : 0 ≤ L := by linarith
    nlinarith [mul_nonneg hC hL0]
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_nonneg _
  · exact Real.exp_nonneg _

theorem PublishedProgressionInput.short_prime_cell_mass_two (P : PublishedProgressionInput) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ q a : ℕ, ∀ u v : ℝ, T ≤ u → v ≤ u + 1 →
      (∑ p ∈ primeLogCellSet q a u v, (p : ℝ)⁻¹) ≤ 2 := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp P.prime_log_cell_upper
  refine ⟨max T 1, le_max_right _ _, ?_⟩
  intro q a u v hu hv
  have hu1 : 1 ≤ u := (le_max_right T 1).trans hu
  have hsub : primeLogCellSet q a u v ⊆ primeLogCellSet 1 0 u (u + 1) := by
    intro p hp
    obtain ⟨hpp, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hp
    exact mem_primeLogCellSet_iff.mpr ⟨hpp, by simp only [Nat.modEq_one], hlo, hhi.trans hv⟩
  apply (hT u ((le_max_left T 1).trans hu) _ hsub).trans
  exact (div_le_iff₀ (by linarith : 0 < u)).mpr (by linarith)

/-- The three original-prior mass premises used by the signed bulk bound
hold simultaneously. No renormalization after idealization is introduced. -/
theorem PublishedProgressionInput.original_harmonic_box_rate (P : PublishedProgressionInput)
    (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (Cell : Type) [Fintype Cell] (Q : ℕ), 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      ∀ (u v : Cell → ℝ) (D : Finset ℕ),
      (∀ c, 1 ≤ u c) → (∀ c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u c) →
      (∀ c, u c ≤ v c) → (∀ c, v c ≤ u c + 1) →
      (∀ c d, c ≠ d → v c ≤ u d ∨ v d ≤ u c) →
      (D.card : ℝ) ≤ Real.exp (C * L) →
      let S := primeCellSupport 1 (fun _ : Cell => 0) u v
      Real.exp (-C * L) ≤ (∑ p ∈ S, (p : ℝ)⁻¹) →
        0 < (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
        (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp ((C + 1) * L) ∧
        (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ *
          (∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹) ≤ 2 := by
  filter_upwards [P.short_cell_mass_error_relative C, deleted_prime_mass_relative_rate C (by linarith),
    retained_prime_normalizer_rate C hC] with L herror hdelete hnorm
  intro Cell _ Q hQ hlog hcard u v D hu hlow huv hshort hsep hD S hmass
  have hS (p) (hp : p ∈ S) : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ) := by
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpp, _, hplog, _⟩ := mem_primeLogCellSet_iff.mp hc
    exact (Real.le_log_iff_exp_le (by exact_mod_cast hpp.pos)).mp ((hlow c).trans hplog.le)
  have hdeleted := hdelete S D _ hD le_rfl hS
  have hm := hnorm S D _ hmass hD le_rfl hS
  refine ⟨hm.1, hm.2, ?_⟩
  exact P.original_harmonic_box_mass Q hQ u v hu huv hshort hsep D _ (Real.exp_pos _)
    hmass hdeleted (herror Cell Q hQ hlog hcard u hlow)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_BulkProgressionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual frequency/spectator modulus fits one progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem bulkProgressionCutoff_bounds (L : ℝ) (hL : 2000 ≤ L) :
    2 ≤ bulkProgressionCutoff L ∧
      Real.log (4 * (bulkProgressionCutoff L : ℝ)) ≤
        2 * Real.exp ((12 / 10000 : ℝ) * L) := by
  have hx : (2 : ℝ) ≤ Real.exp ((12 / 10000 : ℝ) * L) := by
    have hh : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    exact hh.trans (Real.exp_le_exp.mpr (by linarith))
  have hbig : (3 : ℝ) ≤ Real.exp ((12 / 10000 : ℝ) * L) :=
    (by linarith [Real.add_one_le_exp 2] : (3 : ℝ) ≤ Real.exp 2).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hQ : 2 ≤ bulkProgressionCutoff L := by
    apply Nat.le_floor
    exact hx.trans (by linarith [Real.add_one_le_exp (Real.exp ((12 / 10000 : ℝ) * L))])
  refine ⟨hQ, ?_⟩
  have hpos : (0 : ℝ) < bulkProgressionCutoff L := by exact_mod_cast (by omega : 0 < bulkProgressionCutoff L)
  have hf : (bulkProgressionCutoff L : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) :=
    Nat.floor_le (Real.exp_nonneg _)
  have hh := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 4) hpos)
    (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 4))
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hh
  have hlog : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

theorem bulkResidueModulus_unit_card {M Q : ℕ} [NeZero M] (hMQ : M ≤ Q)
    {L : ℝ} (hQ : (Q : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L))) :
    (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) := by
  have hc : Fintype.card (ZMod M)ˣ ≤ M := by
    simpa only [ZMod.card] using Fintype.card_le_of_injective
      (fun u : (ZMod M)ˣ => (u : ZMod M)) Units.val_injective
  exact (Nat.cast_le.mpr (hc.trans hMQ)).trans hQ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternHalfLogWindowPrimeRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One original-prior signed bulk estimate at the manuscript scales -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The three arithmetic costs are combined for the literal original prime
mean. The only analytic input is the published progression theorem; local
cancellation is proved from the balanced spectator sets and their mixed
Fourier bounds. All prime normalizers are those before idealization. -/
theorem PublishedProgressionInput.movingPattern_half_log_original_prime_rate_window
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
      ∀ (Bidx Cidx Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (base : Fin (N + 1) → ℕ) (primes : Finset ℕ)
        (hprimes : ∀ p ∈ primes, p.Prime)
        (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (Qfreq : ℕ) (y X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex (n + 2) × Fin m) → Cell → ℝ)
        (deleted : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
        (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0) →
      (∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → base i ∈ deleted j) →
      (∀ q ∈ outside, q.Prime) → (∀ j q, q ∈ outside → q ∈ deleted j) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      ‖∑ x : (TreeLeafIndex (n + 2) × Fin m) → primes,
        ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
          movingPatternLogPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
            childBound pivotBound hfreq Fw Ew outside R r p
            (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
            y ψ X lo hi hlo hhi φ G XL U logSlots cb x‖ ≤
        Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨ε, δ, hε, hε1, hδ, cutoff, hcutoff, hgain⟩ :=
    exists_movingPatternPrimeGain_window ψ n r₀ A H Bφ Dφ F gain hA hH
  obtain ⟨Cerr, hCerr, hCnorm, hcellRate⟩ :=
    P.movingPattern_half_log_cell_error_rate_window ψ (n + 2) r₀ k A H Bφ Dφ F (Cmass + 1) Dlog hA hH hF hDlog tlog htlog
  obtain ⟨Tcell, _, hcellTwo⟩ := P.short_prime_cell_mass_two
  have hlarge : ∀ᶠ L : ℝ in atTop, Tcell ≤ Real.exp ((39 / 10000 : ℝ) * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))).eventually
      (eventually_ge_atTop Tcell)
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  filter_upwards [hcellRate, movingPattern_bad_event_rate_window ψ (n + 2) r₀ k
    A H Bφ Dφ F (Cmass + 1) hA hH hF,
    P.original_harmonic_box_rate Cmass hCmass, hlarge, eventually_ge_atTop (2000 : ℝ)]
    with L herror hbad hnormal hlarge hL
  dsimp only
  intro lo hi hlo hhi hwidth Bidx Cidx Cell _ N e tierB tierC t small slot perm pattern base primes hprimes hbase
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β Qfreq y X j₀ φ G XL U u v deleted logSlots cb
    hslots hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
  let M := ∏ i, bulkResidueModuli r p i
  let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
    (fun c => u j c.1) (fun c => v j c.1)
  let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
    ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
  let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
    (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
  let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
    Fw Ew data childBound R r P Qfreq y
  let spec := fun i => frozenBulkSpectatorHaar base (n + 2) m t
    (fun b => movingPatternFiniteSmall e (n + 2) (small b))
    (movingPatternFiniteSamples e (n + 2) pattern) (twist i) perm
    (normalizedResidueTransform (sets i))
  let a := fun z => freq (bulkResidueEquiv r p hc z).1 *
    ∏ i, spec i ((bulkResidueEquiv r p hc z).2 i)
  have hamp0 : 0 ≤ amp := by dsimp only [amp]; positivity
  have hg := hgain m hm lo hi hhi hwidth Bidx Cidx N e base t small pattern p hp
    (fun i b s hs => ⟨hfreq b s hs, hfreqp i b s hs⟩) hsmallp hsamplesp
    twist perm hgood sets hdlo hdhi hsets hsetsp β hβ hbias amp hamp0 hamp
  have hQ := bulkProgressionCutoff_bounds L hL
  have hnorm (j) : 0 < (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹) ∧
      Z j ≤ Real.exp ((Cmass + 1) * L) ∧
      Z j * (∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹) ≤ 2 := by
    have heq := unitPrimeCellSupport_eq M (u j) (v j) (hMcell j)
    have hh := hnormal Cell (bulkProgressionCutoff L) hQ.1 hQ.2 hcard
      (u j) (v j) (deleted j) (hu j) (hulow j) (huv j) (hshort j) (hsep j) (hdel j)
    simpa only [← heq, S, Z] using hh (by simpa only [← heq, S] using hmass j)
  have hlow (j) (q : ℕ) (hq : q ∈ S j) :
      Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ) := by
    obtain ⟨c, _, hqc⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqp, _, hql, _⟩ := mem_primeLogCellSet_iff.mp hqc
    exact (Real.le_log_iff_exp_le (by exact_mod_cast hqp.pos)).mp ((hulow j c.1).trans hql.le)
  have hZ0 (j) : 0 ≤ Z j := inv_nonneg.mpr (hnorm j).1.le
  have hZ (j) : Z j ≤ Real.exp (Cerr * L) := (hnorm j).2.1.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCnorm (by linarith)))
  have hunit : (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) :=
    bulkResidueModulus_unit_card hMQ (Nat.floor_le (Real.exp_nonneg _))
  have ha (z) : ‖a z‖ ≤ amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1)) := by
    exact moving_frozen_residue_coefficient_norm base (movingPatternBulkEmbedding e slot) outside
      Fw Ew (n + 2) m data childBound R r P Qfreq y hy p sets hsets hsetsp
      t _ _ twist perm (bulkResidueEquiv r p hc z).1 (bulkResidueEquiv r p hc z).2
  have he := herror lo hi hhi hwidth Cell M (bulkProgressionCutoff L) hQ.1 hQ.2 p Z a amp
    (Real.exp ((39 / 10000 : ℝ) * L)) (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) le_rfl hpupper hZ0 hZ hcard hunit hamp0 hamp ha le_rfl u hulow
  have hbd := hbad lo hi hhi hwidth p S deleted Z amp ((Cmass + 1) * L)
    (Real.exp ((39 / 10000 : ℝ) * L)) hpupper hZ0 (fun j => (hnorm j).2.1)
    (fun j => (hdel j).trans (Real.exp_le_exp.mpr (by nlinarith))) le_rfl hamp0 hamp le_rfl hlow
  have hb := P.movingPattern_log_mixed_prime_signed_bound e tierB tierC t small slot perm pattern
    hsmall hB htier base primes hprimes hbase childBound pivotBound hfreq Fw Ew outside R r
    hR hr p hc (fun i => normalizedResidueTransform (sets i))
    (fun i => normalizedResidueTransform_zero (sets i)) twist (bulkProgressionCutoff L) Qfreq y
    j₀ ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout XL U logSlots cb Dlog hDlog hloglip
    (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) hslots r₀ hsmallLen hy hQ.1 hMQ hpage u v hu huv hshort
    (fun j c z => hcellTwo M z.val.val (u j c) (v j c) (hlarge.trans (hulow j c)) (hshort j c))
    c₀ hS (fun j => unitPrimeCells_separated M (u j) (v j) (hsep j)) deleted
    (fun j => (hnorm j).1.ne') hdelbase hout hdelout (fun i => (p i : ℝ))
    (fun i => Nat.cast_nonneg _) (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z)
    δ hδ.le ((Cmass + 1) * L) (Real.exp ((39 / 10000 : ℝ) * L))
    hg.1 (fun j => (hnorm j).2.2) (fun j => (hnorm j).2.1)
    (fun j q hq => hlow j q (Finset.mem_sdiff.mp hq).1)
  dsimp only at hb
  calc
    _ ≤ _ := hb
    _ ≤ Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
      have hh := add_le_add (add_le_add hg.2 he) hbd
      simpa only [add_assoc, W, amp, Z, a, spec, freq, data, M, S] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bound for the literal original prime observable -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell I : Type*} [Fintype Cell] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
/-- This uniform pointwise estimate allows the extra nonbulk-prime deletion
error to be returned to the initial external law. -/
theorem movingPatternPrimeBulkHaar_norm
    (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : (TreeLeafIndex n × Fin m) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U x‖ ≤
        (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  intro data amp W
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  have hp := primeBulkValues_prime base (movingPatternBulkEmbedding e slot) x hprimes hbase
  have hv : ∀ i, value i ≠ 0 := fun i => (hp i).ne_zero
  have hf := movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq
  let nodes := fun b => (data b).formulaNodes value hv childBound pivotBound (hf b)
    (.prime false) (.prime true)
  have hk : ‖movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U‖ ≤ W := by
    rw [← realValueKernelPair_nat value hv childBound pivotBound data hf]
    exact movingPattern_kernel_norm_le e tierB tierC t small slot perm pattern hB htier
      (fun i => (value i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hV
      φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
  have hfr : ‖movingFrequencyPageAverage value outside F E data nodes R r P Q y‖ ≤ amp :=
    movingFrequencyPageAverage_norm_le value outside F E data nodes R r P Q y hy
  have hs : ‖∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data‖ ≤
      ∏ i, Kspec i ^ (2 ^ (n + 1)) := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ =>
      movingSpectatorHaarAverage_norm_le value (p i) (g i) (twist i) data
        (Kspec i) (hKspec i) (hgnorm i))
  change ‖movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPageAverage value outside F E data nodes R r P Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data)‖ ≤ _
  simp only [norm_mul]
  calc
    _ ≤ W * (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) :=
      mul_le_mul hk (mul_le_mul hfr hs (norm_nonneg _) (by dsimp only [amp]; positivity))
        (by positivity) (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLogPrimeNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bound for the literal original prime observable -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell I : Type*} [Fintype Cell] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
/-- This uniform pointwise estimate allows the extra nonbulk-prime deletion
error to be returned to the initial external law. -/
theorem movingPatternLogPrimeBulkHaar_norm
    (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : (TreeLeafIndex n × Fin m) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternLogPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U logSlots cb x‖ ≤
        (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  intro data amp W
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  have hn : 0 ≤ ∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j) :=
    Finset.prod_nonneg (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
  have hle : (∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j)) ≤ 1 :=
    Finset.prod_le_one (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
      (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).2)
  change ‖((_ : ℝ) : ℂ) * movingPatternPrimeBulkHaar e t small slot perm pattern base
    primes hprimes hbase childBound pivotBound hfreq F E outside R r p g twist P Q y
    ψ X lo hi hlo hhi φ G L U x‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
  apply (mul_le_of_le_one_left (norm_nonneg _) hle).trans
  exact movingPatternPrimeBulkHaar_norm e tierB tierC t small slot perm pattern hB htier
    base primes hprimes hbase childBound pivotBound hfreq F E outside R r p g twist P Q y
    j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U hy Kspec hKspec hgnorm x

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialPrimePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Returning the conditional bulk law to its initial harmonic prior -/

namespace Ostmann
open scoped Classical BigOperators

/-- Deleting primes after fixing nonbulk coordinates does not change the
initial law silently. Its signed mean is controlled by the conditional mean
plus the exact restored-mass cost, with the latter's original normalizer. -/
theorem initial_prime_prior_bound {J : Type*} [Fintype J]
    (P : Finset ℕ) (S D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hnew : ∀ j, 0 < ∑ q ∈ S j \ D j, (q : ℝ)⁻¹)
    (F : (J → P) → ℂ) (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    let Z := fun j => (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹
    ‖∑ x, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) * F x‖ ≤
      ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x‖ +
        B * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) := by
  intro Z
  let oldMass := fun j => ∑ q ∈ S j, (q : ℝ)⁻¹
  let newMass := fun j => ∑ q ∈ S j \ D j, (q : ℝ)⁻¹
  let ρ := fun j => newMass j / oldMass j
  let restored := fun j (q : P) => if (q : ℕ) ∈ S j then Z j * (q : ℝ)⁻¹ else 0
  have hmass (j) : newMass j ≤ oldMass j :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by intros; positivity)
  have hold (j) : 0 < oldMass j := (hnew j).trans_le (hmass j)
  have hρ0 (j) : 0 ≤ ρ j := div_nonneg (hnew j).le (hold j).le
  have hρ1 (j) : ρ j ≤ 1 := (div_le_one (hold j)).mpr (hmass j)
  have hprior (j) (q : P) : primeSubsetPrior P (S j) q = ρ j * restored j q := by
    by_cases hq : (q : ℕ) ∈ S j
    · simp only [primeSubsetPrior, hq, ite_true, if_true, restored]
      dsimp only [ρ, oldMass, newMass, Z]
      field_simp [(hnew j).ne', (hold j).ne']
    · simp only [primeSubsetPrior, hq, ite_false, if_false, restored, mul_zero]
  have heq :
      (∑ x : J → P, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) * F x) =
      ((∏ j, ρ j : ℝ) : ℂ) * ∑ x : J → P, ((∏ j, restored j (x j) : ℝ) : ℂ) * F x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [hprior]
    rw [Finset.prod_mul_distrib, Complex.ofReal_mul, mul_assoc]
  have hρprod : (∏ j, ρ j) ≤ 1 := by
    simpa only [Finset.prod_const_one] using
      Finset.prod_le_prod (fun j (_ : j ∈ (Finset.univ : Finset J)) => hρ0 j) (fun j _ => hρ1 j)
  have hscale : ‖∑ x : J → P, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) * F x‖ ≤
      ‖∑ x : J → P, ((∏ j, restored j (x j) : ℝ) : ℂ) * F x‖ := by
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun j _ => hρ0 j)]
    exact mul_le_of_le_one_left (norm_nonneg _) hρprod
  have hd := original_prime_restoration_difference P S D hSP (fun j => (hnew j).ne') F B hF
  dsimp only at hd
  have ht := norm_le_norm_add_norm_sub
    (∑ x : J → P, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x)
    (∑ x : J → P, ((∏ j, restored j (x j) : ℝ) : ℂ) * F x)
  exact hscale.trans (ht.trans (add_le_add le_rfl hd))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_NestedPrimePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Returning to an initial law that already excludes prescribed primes -/

namespace Ostmann
open scoped Classical BigOperators

/-- Global exclusions made when constructing the word remain excluded.
Only the extra, nonbulk-dependent deletion is undone. The error can still
be charged to the larger shell and its conditional normalizer. -/
theorem nested_prime_prior_bound {J : Type*} [Fintype J]
    (P : Finset ℕ) (S initial D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hsub : ∀ j, initial j ⊆ S j) (hretain : ∀ j, S j \ D j ⊆ initial j)
    (hnew : ∀ j, 0 < ∑ q ∈ S j \ D j, (q : ℝ)⁻¹)
    (F : (J → P) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖∑ x, ((∏ j, primeSubsetPrior P (initial j) (x j) : ℝ) : ℂ) * F x‖ ≤
      ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x‖ +
        B * ((∏ j, (1 + (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹ *
          ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) := by
  have heq (j) : initial j \ D j = S j \ D j := by
    ext q
    constructor
    · intro hq
      exact Finset.mem_sdiff.mpr ⟨hsub j (Finset.mem_sdiff.mp hq).1, (Finset.mem_sdiff.mp hq).2⟩
    · intro hq
      exact Finset.mem_sdiff.mpr ⟨hretain j hq, (Finset.mem_sdiff.mp hq).2⟩
  have hb := initial_prime_prior_bound P initial D (fun j => (hsub j).trans (hSP j))
    (fun j => by simpa only [heq] using hnew j) F B hF
  dsimp only at hb
  simp_rw [heq] at hb
  apply hb.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  apply sub_le_sub_right
  apply Finset.prod_le_prod
  · intro j _
    have hmass : 0 ≤ ∑ q ∈ initial j ∩ D j, (q : ℝ)⁻¹ :=
      Finset.sum_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q)
    positivity
  · intro j _
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hnew j).le)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      exact Finset.mem_inter.mpr ⟨hsub j (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩
    · intros
      positivity

/-- The initial law may retain any prescribed global exclusions between the
full shell and the additionally conditioned law. -/
theorem nested_prime_prior_three_errors {J : Type*} [Fintype J]
    (P : Finset ℕ) (S initial D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hsub : ∀ j, initial j ⊆ S j) (hretain : ∀ j, S j \ D j ⊆ initial j)
    (hnew : ∀ j, 0 < ∑ q ∈ S j \ D j, (q : ℝ)⁻¹)
    (F : (J → P) → ℂ) (B main error tail : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B)
    (hmean : ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x‖ ≤
      main + error + tail)
    (herror : B * ((∏ j, (1 + (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹ *
      ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) ≤ tail) :
    ‖∑ x, ((∏ j, primeSubsetPrior P (initial j) (x j) : ℝ) : ℂ) * F x‖ ≤
      main + error + 2 * tail := by
  apply (nested_prime_prior_bound P S initial D hSP hsub hretain hnew F B hB hF).trans
  exact (add_le_add hmean herror).trans_eq (by ring)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternHalfLogWindowInitialRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed cancellation under the initial, unconditioned bulk law -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_half_log_initial_prime_rate_window
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
      ∀ (Bidx Cidx Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (base : Fin (N + 1) → ℕ) (primes : Finset ℕ)
        (hprimes : ∀ p ∈ primes, p.Prime)
        (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (Qfreq : ℕ) (y X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex (n + 2) × Fin m) → Cell → ℝ)
        (deleted : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
        (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0) →
      (∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → base i ∈ deleted j) →
      (∀ q ∈ outside, q.Prime) → (∀ j q, q ∈ outside → q ∈ deleted j) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      ∀ initial : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ,
      (∀ j, initial j ⊆ S j) → (∀ j, S j \ deleted j ⊆ initial j) →
      ‖∑ x : (TreeLeafIndex (n + 2) × Fin m) → primes,
        ((∏ j, primeSubsetPrior primes (initial j) (x j) : ℝ) : ℂ) *
          movingPatternLogPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
            childBound pivotBound hfreq Fw Ew outside R r p
            (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
            y ψ X lo hi hlo hhi φ G XL U logSlots cb x‖ ≤
        Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hconditional⟩ :=
    P.movingPattern_half_log_original_prime_rate_window ψ n r₀ k A H Bφ Dφ F Cmass gain
      hA hH hF hCmass hBφ hDφ Dlog hDlog hloglip tlog htlog
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  filter_upwards [hconditional, movingPattern_bad_event_rate_window ψ (n + 2) r₀ k
    A H Bφ Dφ F (Cmass + 1) hA hH hF,
    P.original_harmonic_box_rate Cmass hCmass, eventually_ge_atTop (2000 : ℝ)]
    with L hconditional hbad hnormal hL
  dsimp only
  intro lo hi hlo hhi hwidth Bidx Cidx Cell _ N e tierB tierC t small slot perm pattern base primes hprimes hbase
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β Qfreq y X j₀ φ G XL U u v deleted logSlots cb
    hslots hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀ initial hsub hretain
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
  let M := ∏ i, bulkResidueModuli r p i
  let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
    (fun c => u j c.1) (fun c => v j c.1)
  let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
    ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
  let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
    (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
  have hQ := bulkProgressionCutoff_bounds L hL
  have hnorm (j) : 0 < (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹) ∧
      Z j ≤ Real.exp ((Cmass + 1) * L) ∧
      Z j * (∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹) ≤ 2 := by
    have heq := unitPrimeCellSupport_eq M (u j) (v j) (hMcell j)
    have hh := hnormal Cell (bulkProgressionCutoff L) hQ.1 hQ.2 hcard
      (u j) (v j) (deleted j) (hu j) (hulow j) (huv j) (hshort j) (hsep j) (hdel j)
    simpa only [← heq, S, Z] using hh (by simpa only [← heq, S] using hmass j)
  have hlow (j) (q : ℕ) (hq : q ∈ S j) :
      Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ) := by
    obtain ⟨c, _, hqc⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqp, _, hql, _⟩ := mem_primeLogCellSet_iff.mp hqc
    exact (Real.le_log_iff_exp_le (by exact_mod_cast hqp.pos)).mp ((hulow j c.1).trans hql.le)
  have hZ0 (j) : 0 ≤ Z j := inv_nonneg.mpr (hnorm j).1.le
  have hamp0 : 0 ≤ amp := by dsimp only [amp]; positivity
  have hbd := hbad lo hi hhi hwidth p S deleted Z amp ((Cmass + 1) * L)
    (Real.exp ((39 / 10000 : ℝ) * L)) hpupper hZ0 (fun j => (hnorm j).2.1)
    (fun j => (hdel j).trans (Real.exp_le_exp.mpr (by nlinarith))) le_rfl hamp0 hamp le_rfl hlow
  have hdeletedBound := hconditional lo hi hlo hhi hwidth Bidx Cidx Cell N e tierB tierC t small slot perm pattern
    base primes hprimes hbase childBound pivotBound hfreq Fw Ew outside R r p hc twist sets β Qfreq y X
    j₀ φ G XL U u v deleted logSlots cb hslots hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp
    hgood hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀
  let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) * W
  have hpoint (x : (TreeLeafIndex (n + 2) × Fin m) → primes) :
      ‖movingPatternLogPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G XL U logSlots cb x‖ ≤ cost :=
    movingPatternLogPrimeBulkHaar_norm e tierB tierC t small slot perm pattern hB htier
      base primes hprimes hbase childBound pivotBound hfreq Fw Ew outside R r p
      (fun i => normalizedResidueTransform (sets i)) twist P Qfreq y
      j₀ ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout XL U logSlots cb
      hy (fun i => (p i : ℝ)) (fun i => Nat.cast_nonneg _)
      (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z) x
  have hcollision : 0 ≤ cost * (Fintype.card (TreeLeafIndex (n + 2) × Fin m) : ℝ) ^ 2 *
      Real.exp ((Cmass + 1) * L - Real.exp ((39 / 10000 : ℝ) * L)) := by
    dsimp only [cost, W, amp]
    positivity
  have hreturnCost := (le_add_of_nonneg_left hcollision).trans hbd
  have hcost0 : 0 ≤ cost := by dsimp only [cost, W, amp]; positivity
  have hfinal := @nested_prime_prior_three_errors (TreeLeafIndex (n + 2) × Fin m)
    inferInstance primes S initial deleted hS hsub hretain (fun j => (hnorm j).1)
    (fun x => movingPatternLogPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
      childBound pivotBound hfreq Fw Ew outside R r p
      (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
      y ψ X lo hi hlo hhi φ G XL U logSlots cb x)
    cost (Real.exp (-gain * m)) (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)))
    (Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) hcost0 hpoint
    (by simpa only [finite_univ_canonical, m, S, M] using hdeletedBound)
    (by simpa only [finite_univ_canonical, cost, W, m, Z] using hreturnCost)
  simpa only [finite_univ_canonical, m, S, M] using hfinal

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLogPrimeObservable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal prime observable in the original nonbulk Fubini formula -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (L U : ℝ)
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

theorem movingPatternLogPrimeObservable_join (base : Fin (N + 1) → primes)
    (z : TreeLeafIndex n × Fin m → primes) :
    movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U logSlots cb
      (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => base i)) =
    movingPatternLogPrimeBulkHaar e t small slot perm pattern (fun i => (base i : ℕ)) primes
      hprimes (fun i _ => hprimes _ (base i).property) childBound pivotBound hfreq F E outside
      R r p g twist P Q y ψ X lo hi hlo hhi φ G L U logSlots cb z := by
  have hv : (fun i => (joinBulkNonbulk (A := primes) (movingPatternBulkEmbedding e slot) z
      (fun j => base j) i : ℕ)) =
      primeBulkValues (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) z := by
    funext i
    by_cases hi : i ∈ Set.range (movingPatternBulkEmbedding e slot)
    · obtain ⟨j, rfl⟩ := hi
      rw [joinBulkNonbulk_bulk, primeBulkValues_at]
    · rw [joinBulkNonbulk_nonbulk (movingPatternBulkEmbedding e slot) z
        (fun j => base j) ⟨i, hi⟩, primeBulkValues_off _ _ _ i hi]
  let eval : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} → ℂ := fun v =>
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun b => (data b).formulaNodes v.val v.property childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
      (.prime false) (.prime true)
    ((∏ j, bulkLogCutoffWeight (fun i => (v.val i : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
      (movingRealKernelPair v.val data nodes ψ X lo hi hlo hhi φ G L U *
      (movingFrequencyPageAverage v.val outside F E data nodes R r P Q y *
        ∏ i, movingSpectatorHaarAverage v.val (p i) (g i) (twist i) data))
  let left : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} :=
    ⟨fun i => (joinBulkNonbulk (A := primes) (movingPatternBulkEmbedding e slot) z
        (fun j => base j) i : ℕ),
      fun i => (hprimes _ ((joinBulkNonbulk (A := primes)
        (movingPatternBulkEmbedding e slot) z (fun j => base j)) i).property).ne_zero⟩
  let right : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} :=
    ⟨primeBulkValues (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) z,
      fun i => (primeBulkValues_prime (fun i => (base i : ℕ))
        (movingPatternBulkEmbedding e slot) z hprimes
        (fun i _ => hprimes _ (base i).property) i).ne_zero⟩
  change eval left = eval right
  exact congrArg eval (Subtype.ext hv)

/-- This is exactly the selected-coordinate average used by the signed
pattern majorant, under the initial word law. -/
theorem movingPatternBulkMean_logPrimeObservable (base : Fin (N + 1) → primes)
    (ν : B → primes → ℝ) (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
    (hν : ∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) :
    movingPatternBulkMean e ν slot
      (movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U logSlots cb) base =
    ∑ z : TreeLeafIndex n × Fin m → primes,
      ((∏ j, primeSubsetPrior primes (initial j) (z j) : ℝ) : ℂ) *
        movingPatternLogPrimeBulkHaar e t small slot perm pattern (fun i => (base i : ℕ)) primes
          hprimes (fun i _ => hprimes _ (base i).property) childBound pivotBound hfreq F E outside
          R r p g twist P Q y ψ X lo hi hlo hhi φ G L U logSlots cb z := by
  unfold movingPatternBulkMean
  apply Finset.sum_congr rfl
  intro z _
  rw [movingPatternLogPrimeObservable_join]
  simp only [hν]

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternHalfLogWindowSelectedRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published prime estimate in the original selected-coordinate mean -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_half_log_selected_prime_rate_window_oai
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
      ∀ (Bidx Cidx Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (base : Fin (N + 1) → primes)
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (Qfreq : ℕ) (y X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex (n + 2) × Fin m) → Cell → ℝ)
        (deleted : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
        ((base (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ i c, ((base (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (base i : ℕ) ∈ deleted j) →
      (∀ q ∈ outside, q.Prime) → (∀ j q, q ∈ outside → q ∈ deleted j) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      ∀ initial : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ,
      (∀ j, initial j ⊆ S j) → (∀ j, S j \ deleted j ⊆ initial j) →
      ∀ ν : Bidx → primes → ℝ,
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      ‖movingPatternBulkMean e ν slot
        (movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
          childBound pivotBound hfreq Fw Ew outside R r p
          (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
          y ψ X lo hi hlo hhi φ G XL U logSlots cb) base‖ ≤
        Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hrate⟩ :=
    P.movingPattern_half_log_initial_prime_rate_window ψ n r₀ k A H Bφ Dφ F Cmass gain
      hA hH hF hCmass hBφ hDφ Dlog hDlog hloglip tlog htlog
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  filter_upwards [hrate] with L hrate
  dsimp only
  intro lo hi hlo hhi hwidth Bidx Cidx Cell _ N e tierB tierC t small slot perm pattern primes hprimes base
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β Qfreq y X j₀ φ G XL U u v deleted logSlots cb
    hslots hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀ initial hsub hretain ν hν
  rw [movingPatternBulkMean_logPrimeObservable]
  · exact hrate lo hi hlo hhi hwidth Bidx Cidx Cell N e tierB tierC t small slot perm pattern
      (fun i => (base i : ℕ)) primes hprimes (fun i _ => hprimes _ (base i).property)
      childBound pivotBound hfreq Fw Ew outside R r p hc twist sets β Qfreq y X j₀ φ G XL U u v deleted logSlots cb
      hslots hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
      hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
      hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀ initial hsub hretain
  · exact hν

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_selected_prime_rate_window_oai := @OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_selected_prime_rate_window_oai
