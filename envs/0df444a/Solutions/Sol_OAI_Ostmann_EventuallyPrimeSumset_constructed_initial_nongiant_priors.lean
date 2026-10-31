-- Prove2me | solution 1 for OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:55:43.052088+00:00
-- url     : https://prove2.me/submissions/b7b65c2f-5ebf-4127-b674-b3a1e8932436

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_initial_broad_prior_centers

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteCellMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Means on the actual fibers of a finite partition -/

namespace Ostmann

open scoped BigOperators Classical

theorem finiteCellMass_nonneg (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ p ∈ P, 0 ≤ μ p) (h : ℕ) : 0 ≤ finiteCellMass P label μ h := by
  exact Finset.sum_nonneg (fun p hp => hμ p (Finset.mem_filter.mp hp).1)

theorem finiteCellMass_sum (P I : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (hlabel : ∀ p ∈ P, label p ∈ I) :
    (∑ h ∈ I, finiteCellMass P label μ h) = ∑ p ∈ P, μ p := by
  exact Finset.sum_fiberwise_of_maps_to hlabel μ

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

theorem log_unit_ratio_lower {s : ℝ} (hs : 0 < s) :
    1 / (s + 1) ≤ Real.log ((s + 1) / s) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := (s + 1) / s)
    (div_pos (by linarith) hs)
  have heq : 1 - ((s + 1) / s)⁻¹ = 1 / (s + 1) := by
    field_simp
    ring
  rwa [heq] at h

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

theorem PublishedProgressionInput.ordinary_interval_lower (P : PublishedProgressionInput) :
    ∀ᶠ s : ℝ in atTop,
      1 / (2 * (s + 1)) ≤ reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp (s + 1)) := by
  filter_upwards [theta_log_error_small P.errorConstant P.decay P.decay_pos,
    eventually_ge_atTop (1 : ℝ)] with s herr hs
  have h := P.ordinary_log_interval hs (by linarith : s ≤ s + 1) le_rfl
  have hlower := log_unit_ratio_lower (by linarith : 0 < s)
  have hhalf : 1 / (s + 1) = 2 * (1 / (2 * (s + 1))) := by field_simp
  have hh := (abs_le.mp h).1
  linarith

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prime log cells and their means -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem primeLogIndex_bounds (p : ℕ) (hp : p.Prime) :
    (primeLogIndex p : ℝ) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ (primeLogIndex p : ℝ) + 1 := by
  have hx : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  let n := ⌈Real.log (p : ℝ)⌉₊
  have hn : 0 < n := by
    have h := Nat.le_ceil (Real.log (p : ℝ))
    by_contra! hz
    have he : n = 0 := Nat.eq_zero_of_le_zero hz
    change Real.log (p : ℝ) ≤ (n : ℝ) at h
    rw [he, Nat.cast_zero] at h
    linarith
  have heq : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
  have hu := Nat.le_ceil (Real.log (p : ℝ))
  have hl := Nat.ceil_lt_add_one hx.le
  change (n : ℝ) < Real.log (p : ℝ) + 1 at hl
  change Real.log (p : ℝ) ≤ (n : ℝ) at hu
  change ((n - 1 : ℕ) : ℝ) < Real.log (p : ℝ) ∧
    Real.log (p : ℝ) ≤ ((n - 1 : ℕ) : ℝ) + 1
  constructor <;> linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem primeSubsetPrior_atom (P Q : Finset ℕ) (p : P) :
    primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := by
  unfold primeSubsetPrior
  split_ifs
  · exact le_of_eq (by ring)
  · positivity

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCellChoice
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer cell centers outside a finite set of failures -/

namespace Ostmann
open scoped Classical

theorem nat_cell_center_avoiding (D : Finset ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ c : ℕ, c ∉ D ∧ T ≤ (c : ℝ) ∧ (c : ℝ) ≤ T + D.card + 1 := by
  let a := ⌈T⌉₊
  let S := (Finset.range (D.card + 1)).image (fun j => a + j)
  have hcard : S.card = D.card + 1 := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range _
    · exact fun _ _ hij => Nat.add_left_cancel hij
  have hex : ∃ c ∈ S, c ∉ D := by
    by_contra! h
    have hc := Finset.card_le_card (show S ⊆ D from h)
    omega
  obtain ⟨c, hc, hnot⟩ := hex
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
  have hjR : (j : ℝ) ≤ D.card := by
    exact_mod_cast (show j ≤ D.card from Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  refine ⟨a + j, hnot, ?_, ?_⟩
  · push_cast
    exact (Nat.le_ceil T).trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  · push_cast
    have ha : (a : ℝ) < T + 1 := Nat.ceil_lt_add_one hT
    linarith

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTargetTotal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards target construction preserves the original total log size -/

namespace Ostmann
open scoped BigOperators

theorem movingCompensationTargetError_ofFn (k : ℕ) (d : Fin k → ℝ) :
    movingCompensationTargetError (List.ofFn d) = ∑ i : Fin k, (2 : ℝ) ^ (i : ℕ) * d i := by
  induction k with
  | zero => simp [movingCompensationTargetError]
  | succ k ih =>
    rw [List.ofFn_succ, movingCompensationTargetError, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    calc
      _ = d 0 + ∑ i : Fin k, 2 * (2 ^ (i : ℕ) * d i.succ) := by
        rw [← Finset.mul_sum]
        ring
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring

theorem movingCompensationTargetError_gaps (k : ℕ) (BD Bz L : ℝ) :
    movingCompensationTargetError (movingCompensationGaps k BD Bz L) =
      ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ))
        (spectatorBulkCount k L) := by
  unfold movingCompensationGaps
  rw [movingCompensationTargetError_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have hr : (2 : ℝ) ^ (i : ℕ) ≠ 0 := by positivity
  field_simp

theorem moving_protected_and_compensation_total (k : ℕ) (BD Bz L logX G td Δ₀ : ℝ) :
    let gaps := movingCompensationGaps k BD Bz L
    let J := movingProtectedTarget k logX G td
      (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L))
    2 * G + 2 * td + J + (movingCompensationTargets J gaps).sum = logX + Δ₀ := by
  intro gaps J
  have hs := movingCompensationTargets_sum J gaps
  have hlen : gaps.length = k := movingCompensationGaps_length k BD Bz L
  rw [hlen, movingCompensationTargetError_gaps] at hs
  have hJ : (2 : ℝ) ^ k * J = logX - 2 * G - 2 * td +
      (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)) := by
    dsimp [J, movingProtectedTarget]
    field_simp
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeWordCellGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact real cells for the selected harmonic word laws -/

namespace Ostmann
open scoped Classical

theorem primeLogIndex_eq_iff (p h : ℕ) (hp : p.Prime) :
    primeLogIndex p = h ↔ (h : ℝ) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ (h : ℝ) + 1 := by
  constructor
  · intro heq
    simpa only [heq] using primeLogIndex_bounds p hp
  · intro hh
    have hi := primeLogIndex_bounds p hp
    by_contra heq
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · have hb : (primeLogIndex p : ℝ) + 1 ≤ h := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      linarith
    · have hb : (h : ℝ) + 1 ≤ primeLogIndex p := by
        exact_mod_cast Nat.succ_le_of_lt hgt
      linarith

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BadPrimeLogCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic imbalance budget excludes only linearly many cells -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem finiteCellMass_sum_le (P I : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ p ∈ P, 0 ≤ μ p) :
    (∑ h ∈ I, finiteCellMass P label μ h) ≤ ∑ p ∈ P, μ p := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (show I ⊆ I ∪ P.image label from Finset.subset_union_left)
    (fun h _ _ => finiteCellMass_nonneg P label μ hμ h)
  exact h.trans_eq (finiteCellMass_sum P (I ∪ P.image label) label μ
    (fun p hp => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))

theorem badPrimeLogCells_card (I badPrimes : Finset ℕ)
    (hprime : ∀ p ∈ badPrimes, p.Prime) :
    (badPrimeLogCells I badPrimes).card / (16 : ℝ) ≤
      ∑ p ∈ badPrimes, Real.log (p : ℝ) / p := by
  have hcell (h : ℕ) (hh : h ∈ badPrimeLogCells I badPrimes) :
      (1 / 16 : ℝ) ≤ finiteCellMass badPrimes primeLogIndex
        (fun p => Real.log (p : ℝ) / p) h := by
    obtain ⟨_, hh1, hmass⟩ := Finset.mem_filter.mp hh
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    have hmul := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg h (α := ℝ))
    have hlog : (h : ℝ) * finiteCellMass badPrimes primeLogIndex
        (fun p => (p : ℝ)⁻¹) h ≤
        finiteCellMass badPrimes primeLogIndex (fun p => Real.log (p : ℝ) / p) h := by
      unfold finiteCellMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpB, hph⟩ := Finset.mem_filter.mp hp
      have hbound := (primeLogIndex_bounds p (hprime p hpB)).1
      rw [hph] at hbound
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hbound.le
        (inv_nonneg.mpr (Nat.cast_nonneg p))
    have hn : (1 / 16 : ℝ) ≤ (h : ℝ) * (1 / (8 * ((h : ℝ) + 1))) := by
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity : 0 < 8 * ((h : ℝ) + 1))).mpr
      linarith
    exact hn.trans (hmul.trans hlog)
  have hs := Finset.sum_le_sum hcell
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hsum := finiteCellMass_sum_le badPrimes (badPrimeLogCells I badPrimes)
    primeLogIndex (fun p => Real.log (p : ℝ) / p) (fun p hp => by
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le))
        (Nat.cast_nonneg p))
  calc
    _ = (badPrimeLogCells I badPrimes).card * (1 / 16 : ℝ) := by ring
    _ ≤ _ := hs.trans hsum

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GoodPrimeLogCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A cell outside the imbalance failures retains harmonic mass -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem prime_log_cell_good_mass (I badPrimes : Finset ℕ) (h : ℕ)
    (hhI : h ∈ I) (hh1 : 1 ≤ h) (hgood : h ∉ badPrimeLogCells I badPrimes)
    (hfull : 1 / (2 * ((h : ℝ) + 1)) ≤
      ∑ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1), (p : ℝ)⁻¹) :
    1 / (4 * ((h : ℝ) + 1)) ≤
      ∑ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1) \ badPrimes, (p : ℝ)⁻¹ := by
  let Q := primeLogCellSet 1 0 h ((h : ℝ) + 1)
  have hsmall : finiteCellMass badPrimes primeLogIndex (fun p => (p : ℝ)⁻¹) h <
      1 / (8 * ((h : ℝ) + 1)) := by
    by_contra! hn
    exact hgood (Finset.mem_filter.mpr ⟨hhI, hh1, hn⟩)
  have hsub : Q.filter (fun p => p ∈ badPrimes) ⊆
      badPrimes.filter (fun p => primeLogIndex p = h) := by
    intro p hp
    obtain ⟨hpQ, hpB⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, _, hpL⟩ := mem_primeLogCellSet_iff.mp hpQ
    exact Finset.mem_filter.mpr ⟨hpB, (primeLogIndex_eq_iff p h hpP).mpr hpL⟩
  have hbad : (∑ p ∈ Q.filter (fun p => p ∈ badPrimes), (p : ℝ)⁻¹) <
      1 / (8 * ((h : ℝ) + 1)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans_lt hsmall
  have hsplit : (∑ p ∈ Q, (p : ℝ)⁻¹) =
      (∑ p ∈ Q \ badPrimes, (p : ℝ)⁻¹) +
        ∑ p ∈ Q.filter (fun p => p ∈ badPrimes), (p : ℝ)⁻¹ := by
    simp only [Finset.sdiff_eq_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p ∈ badPrimes <;> simp [hp]
  have hidentity : 1 / (2 * ((h : ℝ) + 1)) =
      2 * (1 / (4 * ((h : ℝ) + 1))) ∧
      1 / (8 * ((h : ℝ) + 1)) = (1 / (4 * ((h : ℝ) + 1))) / 2 := by
    constructor <;> field_simp <;> ring
  have hpos : 0 ≤ 1 / (4 * ((h : ℝ) + 1)) := by positivity
  change 1 / (4 * ((h : ℝ) + 1)) ≤ ∑ p ∈ Q \ badPrimes, (p : ℝ)⁻¹
  change 1 / (2 * ((h : ℝ) + 1)) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ at hfull
  rw [hidentity.1] at hfull
  rw [hidentity.2] at hbad
  linarith

theorem PublishedProgressionInput.good_prime_log_cell_mass (P : PublishedProgressionInput) :
    ∃ H : ℝ, ∀ (h : ℕ), H ≤ h → ∀ I badPrimes : Finset ℕ,
      h ∈ I → h ∉ badPrimeLogCells I badPrimes →
      1 / (4 * ((h : ℝ) + 1)) ≤
        ∑ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1) \ badPrimes, (p : ℝ)⁻¹ := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp P.ordinary_interval_lower
  refine ⟨max H 1, ?_⟩
  intro h hh I badPrimes hhI hgood
  have hh1 : 1 ≤ h := by exact_mod_cast (le_max_right H 1).trans hh
  apply prime_log_cell_good_mass I badPrimes h hhI hh1 hgood
  rw [sum_primeLogCellSet_reciprocal]
  exact hH h ((le_max_left H 1).trans hh)

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDefectSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small collision defect forces balanced supports and accurate tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem reciprocal_gap_forces_thirds (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsum : a + b = p) (hgap : p * (1 / a + 1 / b - 4 / p) ≤ 1 / 4) :
    p / 3 ≤ a ∧ a ≤ 2 * p / 3 := by
  have hp : 0 < p := by linarith
  have hab : 0 < a * b := mul_pos ha hb
  have hid : p * (1 / a + 1 / b - 4 / p) = (a - b) ^ 2 / (a * b) := by
    field_simp
    rw [← hsum]
    ring
  have hsq : (a - b) ^ 2 ≤ (1 / 4 : ℝ) * (a * b) := by
    apply (div_le_iff₀ hab).mp
    rwa [← hid]
  constructor
  · by_contra! h
    have hba : 0 ≤ b - 2 * a := by linarith
    have hab' : 0 ≤ 2 * b - a := by linarith
    nlinarith [mul_nonneg hba hab']
  · by_contra! h
    have hab' : 0 ≤ a - 2 * b := by linarith
    have hba : 0 ≤ 2 * a - b := by linarith
    nlinarith [mul_nonneg hab' hba]

theorem small_defect_balances_supports (p : ℕ) (S T : Finset ℕ) (μ ν : ℕ → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) (hcard : S.card + T.card = p)
    (hsmall : (p : ℝ) * collisionDefect p S T μ ν ≤ 1 / 4) :
    (p : ℝ) / 3 ≤ S.card ∧ (S.card : ℝ) ≤ 2 * p / 3 := by
  apply reciprocal_gap_forces_thirds (S.card : ℝ) T.card p
    (by exact_mod_cast hS.card_pos) (by exact_mod_cast hT.card_pos) (by exact_mod_cast hcard)
  have henergy : 0 ≤ (∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) ^ 2) +
      ∑ r ∈ T, (ν r - 1 / (T.card : ℝ)) ^ 2 := by positivity
  have hm := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) henergy
  unfold collisionDefect at hsmall
  nlinarith only [hsmall, hm]

/-- Weighted Markov bound, used with cost `p * collisionDefect`. -/
theorem weighted_cost_exception_bound (P : Finset ℕ) (w cost : ℕ → ℝ) (δ : ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hcost : ∀ p ∈ P, 0 ≤ cost p) :
    δ * (∑ p ∈ P.filter (fun p => δ < cost p), w p) ≤ ∑ p ∈ P, w p * cost p := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ P.filter (fun p => δ < cost p), w p * cost p := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp'.2.le (hw p hp'.1)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p hp _ => mul_nonneg (hw p hp) (hcost p hp))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CollisionPrimeCellBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good cells from the proved collision-stability budget -/

namespace Ostmann
open scoped Classical BigOperators

theorem collisionExceptionalPrimes_log_mass (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) (E : ℝ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card ≤ p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    (∑ p ∈ collisionExceptionalPrimes P S T μ ν, Real.log (p : ℝ) / p) ≤ 4 * E := by
  have h := weighted_cost_exception_bound P (fun p => Real.log (p : ℝ) / p)
    (fun p => (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) (1 / 4)
    (fun p hp => div_nonneg (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le))
      (Nat.cast_nonneg _))
    (fun p hp => mul_nonneg (Nat.cast_nonneg _)
      (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p hp)))
  have heq : (∑ p ∈ P, Real.log (p : ℝ) / p *
      ((p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p))) =
      ∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
    field_simp
  rw [heq] at h
  change (1 / 4 : ℝ) * (∑ p ∈ collisionExceptionalPrimes P S T μ ν,
    Real.log (p : ℝ) / p) ≤ _ at h
  linarith

theorem collision_bad_cell_count (P I : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) (E : ℝ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card ≤ p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    ((badPrimeLogCells I (collisionExceptionalPrimes P S T μ ν)).card : ℝ) ≤ 64 * E := by
  have hm := collisionExceptionalPrimes_log_mass P S T μ ν E hprime hS hT hcard hbudget
  have hc := badPrimeLogCells_card I (collisionExceptionalPrimes P S T μ ν)
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
  linarith

theorem collision_retained_prime_balanced (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (p : ℕ) (hp : p ∈ P \ collisionExceptionalPrimes P S T μ ν) :
    (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3 := by
  obtain ⟨hpP, hpnot⟩ := Finset.mem_sdiff.mp hp
  have hsmall : (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) ≤ 1 / 4 := by
    by_contra! hh
    exact hpnot (Finset.mem_filter.mpr ⟨hpP, hh⟩)
  exact small_defect_balances_supports p (S p) (T p) (μ p) (ν p)
    (hS p hpP) (hT p hpP) (hcard p hpP) hsmall

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CollisionCellChoice
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nearby cell with balanced retained primes -/

namespace Ostmann
open scoped Classical BigOperators

/-- The collision estimate and the published ordinary prime interval estimate
give a cell near every sufficiently large prescribed center. -/
theorem PublishedProgressionInput.collision_cell_near (P0 : PublishedProgressionInput) :
    ∃ H : ℝ, ∀ (P : Finset ℕ) (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
      (E target : ℝ), 0 ≤ E → H ≤ target →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, (S p).Nonempty) → (∀ p ∈ P, (T p).Nonempty) →
      (∀ p ∈ P, (S p).card + (T p).card = p) →
      (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E →
      (∀ h : ℕ, target ≤ h → (h : ℝ) ≤ target + 64 * E + 1 →
        primeLogCellSet 1 0 h ((h : ℝ) + 1) ⊆ P) →
      ∃ h : ℕ, target ≤ h ∧ (h : ℝ) ≤ target + 64 * E + 1 ∧
        1 / (4 * ((h : ℝ) + 1)) ≤
          ∑ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1) \
            collisionExceptionalPrimes P S T μ ν, (p : ℝ)⁻¹ ∧
        (∀ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1) \
            collisionExceptionalPrimes P S T μ ν,
          (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨H, hmass⟩ := P0.good_prime_log_cell_mass
  refine ⟨max H 1, ?_⟩
  intro P S T μ ν E target hE ht hprime hS hT hcard hbudget hcover
  let I := Finset.range ⌈target + 64 * E + 2⌉₊
  let bad := collisionExceptionalPrimes P S T μ ν
  let D := badPrimeLogCells I bad
  have hD : (D.card : ℝ) ≤ 64 * E :=
    collision_bad_cell_count P I S T μ ν E hprime hS hT (fun p hp => (hcard p hp).le) hbudget
  have ht0 : 0 ≤ target := by linarith [(le_max_right H 1).trans ht]
  obtain ⟨h, hgood, hlo, hhi⟩ := nat_cell_center_avoiding D target ht0
  have hupper : (h : ℝ) ≤ target + 64 * E + 1 := by linarith
  have hhI : h ∈ I := by
    apply Finset.mem_range.mpr
    have hceil := Nat.le_ceil (target + 64 * E + 2)
    have hh : (h : ℝ) < (⌈target + 64 * E + 2⌉₊ : ℕ) := by linarith
    exact_mod_cast hh
  refine ⟨h, hlo, hupper, hmass h ((le_max_left H 1).trans (ht.trans hlo)) I bad hhI hgood, ?_⟩
  intro p hp
  obtain ⟨hpQ, hpbad⟩ := Finset.mem_sdiff.mp hp
  exact collision_retained_prime_balanced P S T μ ν hS hT hcard p
    (Finset.mem_sdiff.mpr ⟨hcover h hlo hupper hpQ, hpbad⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordCopyCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two copies of every word and cell role as one ordered tuple -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem productPrior_append {A : Type*} {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ) (x : Fin k → A) (y : Fin m → A) :
    productPrior (Fin.append μ ν) (Fin.append x y) = productPrior μ x * productPrior ν y := by
  simp only [productPrior, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialLogSumBins
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual logarithmic cutoff weights in the initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

theorem balancedTupleSet_mass {A : Type*} [Fintype A] (n : ℕ)
    (μ : Fin n → A → ℝ) (good : Fin n → A → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hmass : ∀ i, δ ≤ ∑ a, if good i a then μ i a else 0) :
    δ ^ n ≤ ∑ x ∈ balancedTupleSet n good, productPrior μ x := by
  have he (x : Fin n → A) :
      (∏ i, if good i (x i) then μ i (x i) else 0) =
        if ∀ i, good i (x i) then productPrior μ x else 0 := by
    by_cases h : ∀ i, good i (x i)
    · simp [h, productPrior]
    · rw [ite_eq_right h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  have hs : (∑ x ∈ balancedTupleSet n good, productPrior μ x) =
      ∏ i, ∑ a, if good i a then μ i a else 0 := by
    simp only [balancedTupleSet, Finset.sum_filter]
    simp_rw [← he]
    exact (Fintype.prod_sum (fun i a => if good i a then μ i a else 0)).symm
  rw [hs]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (fun _ _ => hδ) (fun i _ => hmass i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfListWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent cutoff weights in an initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

/-- Joining the bulk and spectator groups preserves the two weights and
both balanced events under their original independent priors. -/
theorem balancedHalfMass_append {A : Type*} [Fintype A] (b d : ℕ)
    (μ : Fin b → A → ℝ) (ν : Fin d → A → ℝ)
    (goodB : Fin b → A → Prop) (goodD : Fin d → A → Prop)
    (wB : (Fin b → A) → ℝ) (wD : (Fin d → A) → ℝ) :
    (∑ x ∈ balancedTupleSet (b + d) (Fin.append goodB goodD),
      productPrior (Fin.append μ ν) x *
        (wB (fun i => x (i.castAdd d)) * wD (fun i => x (i.natAdd b)))) =
      (∑ x ∈ balancedTupleSet b goodB, productPrior μ x * wB x) *
        ∑ x ∈ balancedTupleSet d goodD, productPrior ν x * wD x := by
  simp only [balancedTupleSet, Finset.sum_filter]
  let e : (Fin b → A) × (Fin d → A) ≃ (Fin (b + d) → A) := Fin.appendEquiv b d
  rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change (if ∀ i, Fin.append goodB goodD i (Fin.append x y i) then
      productPrior (Fin.append μ ν) (Fin.append x y) *
        (wB (fun i => Fin.append x y (i.castAdd d)) * wD (fun i => Fin.append x y (i.natAdd b)))
      else 0) = _
  simp only [Fin.forall_fin_add, Fin.append_left, Fin.append_right, productPrior_append]
  by_cases hB : ∀ i, goodB i (x i) <;> by_cases hD : ∀ i, goodD i (y i) <;>
    simp [hB, hD]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialBalancedCellWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two cutoff weights followed by balanced small cells -/

namespace Ostmann
open scoped Classical BigOperators

theorem balancedTupleSet_mass_one {A : Type*} [Fintype A] (n : ℕ)
    (μ : Fin n → A → ℝ) (good : Fin n → A → Prop)
    (hmass : ∀ i, ∑ p, μ i p = 1)
    (hgood : ∀ i p, μ i p ≠ 0 → good i p) :
    1 ≤ ∑ x ∈ balancedTupleSet n good, productPrior μ x := by
  have hi (i : Fin n) : (∑ p, if good i p then μ i p else 0) = 1 := by
    rw [← hmass i]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hg : good i p
    · simp only [ite_eq_left hg]
    · have hz : μ i p = 0 := by contrapose! hg; exact hgood i p hg
      simp only [ite_eq_right hg, hz]
  simpa only [one_pow] using balancedTupleSet_mass n μ good 1 (by norm_num) (fun i => (hi i).ge)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedInitialCutoffMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Attach small cells after choosing the two broad cutoff centers -/
namespace Ostmann
open scoped Classical BigOperators

/-- The centers are fixed before the top and compensation priors are selected.
Their balanced masses therefore remain available when the cells depend on them. -/
theorem initial_balanced_cell_mass_at (P : Finset ℕ) (b d r m : ℕ)
    (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (gb : Fin b → P → Prop) (gd : Fin d → P → Prop) (gc : Fin r → P → Prop)
    (cb cd : ℝ)
    (hB : Real.exp (-(Real.log 2 + 2) * m) ≤
      ∑ x ∈ balancedTupleSet b gb, productPrior μb x *
        initialLogSumWeight (fun p : P => (p : ℕ)) cb x)
    (hD : Real.exp (-(Real.log 2 + 2) * m) ≤
      ∑ x ∈ balancedTupleSet d gd, productPrior μd x *
        initialLogSumWeight (fun p : P => (p : ℕ)) cd x)
    (hmc : ∀ i, ∑ p, μc i p = 1)
    (hgc : ∀ i p, μc i p ≠ 0 → gc i p) :
    Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
      ∑ x ∈ balancedTupleSet (b + (d + r)) (Fin.append gb (Fin.append gd gc)),
        productPrior (Fin.append μb (Fin.append μd μc)) x *
          (initialLogSumWeight (fun p : P => (p : ℕ)) cb (fun i => x (i.castAdd (d + r))) *
            initialLogSumWeight (fun p : P => (p : ℕ)) cd
              (fun i => x ((i.castAdd r).natAdd b))) := by
  have hcmass := balancedTupleSet_mass_one r μc gc hmc hgc
  let Bmass := ∑ x ∈ balancedTupleSet b gb, productPrior μb x *
    initialLogSumWeight (fun p : P => (p : ℕ)) cb x
  let Dmass := ∑ x ∈ balancedTupleSet d gd, productPrior μd x *
    initialLogSumWeight (fun p : P => (p : ℕ)) cd x
  let Cmass := ∑ x ∈ balancedTupleSet r gc, productPrior μc x
  change Real.exp (-(Real.log 2 + 2) * m) ≤ Bmass at hB
  change Real.exp (-(Real.log 2 + 2) * m) ≤ Dmass at hD
  change 1 ≤ Cmass at hcmass
  have hCD := balancedHalfMass_append d r μd μc gd gc
    (initialLogSumWeight (fun p : P => (p : ℕ)) cd) (fun _ => 1)
  simp only [mul_one] at hCD
  have hfull := balancedHalfMass_append b (d + r) μb (Fin.append μd μc) gb (Fin.append gd gc)
    (initialLogSumWeight (fun p : P => (p : ℕ)) cb)
    (fun y => initialLogSumWeight (fun p : P => (p : ℕ)) cd (fun i => y (i.castAdd r)))
  rw [hCD] at hfull
  rw [hfull]
  change Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤ Bmass * (Dmass * Cmass)
  have hb0 : 0 ≤ Bmass := (Real.exp_nonneg _).trans hB
  have hd0 : 0 ≤ Dmass := (Real.exp_nonneg _).trans hD
  calc
    _ = Real.exp (-(Real.log 2 + 2) * m) * Real.exp (-(Real.log 2 + 2) * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Bmass * Dmass := mul_le_mul hB hD (Real.exp_nonneg _) hb0
    _ ≤ Bmass * (Dmass * Cmass) := by nlinarith [mul_nonneg hb0 hd0]

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCellMassRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The chosen small cells meet the original prior's exponential budget -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_cell_harmonic_floor :
    ∀ᶠ L : ℝ in atTop, ∀ h : ℕ, (h : ℝ) ≤ Real.exp (L / 2) →
      Real.exp (-L) ≤ 1 / (4 * ((h : ℝ) + 1)) := by
  filter_upwards [eventually_ge_atTop (max 0 (2 * Real.log 8))] with L hL h hh
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have he1 : 1 ≤ Real.exp (L / 2) := Real.one_le_exp (by positivity)
  have he8 : 8 ≤ Real.exp (L / 2) := by
    have hh := Real.exp_le_exp.mpr (show Real.log 8 ≤ L / 2 by
      have := (le_max_right (0 : ℝ) (2 * Real.log 8)).trans hL
      linarith)
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 8)] at hh
  have hden : 4 * ((h : ℝ) + 1) ≤ Real.exp L := by
    have he : Real.exp (L / 2) * Real.exp (L / 2) = Real.exp L := by
      rw [← Real.exp_add]; congr 1; ring
    have hm := mul_le_mul_of_nonneg_right he8 (Real.exp_nonneg (L / 2))
    nlinarith only [hh, he1, hm, he]
  have hi := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < 4 * ((h : ℝ) + 1)) hden
  simpa only [one_div, ← Real.exp_neg] using hi

theorem selected_cell_after_finite_deletion :
    ∀ᶠ L : ℝ in atTop, ∀ (h : ℕ) (Q D : Finset ℕ),
      Real.exp ((39 / 10000 : ℝ) * L) ≤ h → (h : ℝ) ≤ Real.exp (L / 2) →
      Q ⊆ primeLogCellSet 1 0 h ((h : ℝ) + 1) →
      1 / (4 * ((h : ℝ) + 1)) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ →
      (D.card : ℝ) ≤ Real.exp L →
      Real.exp (-(2 * L)) ≤ ∑ p ∈ Q \ D, (p : ℝ)⁻¹ ∧
      0 < (∑ p ∈ Q \ D, (p : ℝ)⁻¹) ∧
      (∑ p ∈ Q \ D, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * L) := by
  filter_upwards [eventual_cell_harmonic_floor,
    retained_prime_normalizer_rate 1 (by norm_num)] with L hfloor hnormal
  intro h Q D hhlo hhhi hQ hmass hD
  have hn := hnormal Q D h (by simpa using (hfloor h hhhi).trans hmass)
    (by simpa only [one_mul] using hD) hhlo (fun p hp => by
      obtain ⟨hpprime, _, hlog, _⟩ := mem_primeLogCellSet_iff.mp (hQ hp)
      exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast hpprime.pos)).mp hlog).le)
  have hinv : (∑ p ∈ Q \ D, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * L) := by
    simpa only [show (1 + 1 : ℝ) = 2 by norm_num] using hn.2
  have hlo := inv_anti₀ (inv_pos.mpr hn.1) hinv
  refine ⟨?_, hn.1, hinv⟩
  simpa only [inv_inv, ← Real.exp_neg] using hlo

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailGoodPrimeCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nearby balanced cells for the actual summand tails -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.tail_good_prime_cells_at
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∃ H : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      ∀ target : ℝ, H ≤ target →
      target + 64 * tailDefectBudget a C L + 2 ≤ Real.log (tailCollisionCutoff L : ℝ) →
      ∃ j : ℕ, target ≤ j ∧ (j : ℝ) ≤ target + 64 * tailDefectBudget a C L + 1 ∧
        1 / (4 * ((j : ℝ) + 1)) ≤
          ∑ p ∈ primeLogCellSet 1 0 j ((j : ℝ) + 1) \
            tailCellExceptionalPrimes A B N (summandTailCutoff L) hi (tailCollisionCutoff L),
            (p : ℝ)⁻¹ ∧
        (∀ p ∈ primeLogCellSet 1 0 j ((j : ℝ) + 1) \
            tailCellExceptionalPrimes A B N (summandTailCutoff L) hi (tailCollisionCutoff L),
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
            ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨H, hchoose⟩ := P0.collision_cell_near
  refine ⟨a, ha, H, ?_⟩
  filter_upwards [hlarge, eventual_tailCollisionCutoff N] with L hlarge hcut
  intro hi hhi
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge hi hhi
  let Q := tailCollisionCutoff L
  let P := Nat.primesLE Q
  let S := tailSupport A N
  let T := fun p => Finset.range p \ tailSupport A N p
  let μ := fun p => residueMass (summandTail A (summandTailCutoff L) hi)
    (fun _ => 1 / ((summandTail A (summandTailCutoff L) hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B (summandTailCutoff L) hi)
    (fun _ => 1 / ((summandTail B (summandTailCutoff L) hi).card : ℝ)) (negativeResidue p)
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesLE hp
  have hS : ∀ p ∈ P, (S p).Nonempty := fun p hp =>
    tailSupport_nonempty hA N p (hprime p hp).pos
  have hT : ∀ p ∈ P, (T p).Nonempty := fun p hp =>
    tailSupport_complement_nonempty hB (hprime p hp).pos (hN p (hprime p hp))
  have hcard : ∀ p ∈ P, (S p).card + (T p).card = p :=
    fun p _ => tailSupport_card_add_complement A N p
  have hbudget : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ tailDefectBudget a C L := by
    apply uniform_tail_collision_bound hA hB N (summandTailCutoff L) hi a L C
      ha hcut.1 hcut.2.1 hhi hcut.2.2
      (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
    · simpa only [positiveSummandTail_card] using hsa
    · simpa only [negativeSummandTail_card] using hsb
    · exact hM
  have hE : 0 ≤ tailDefectBudget a C L := le_trans
    (Finset.sum_nonneg fun p hp => mul_nonneg (Real.log_natCast_nonneg p)
      (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p hp).le)) hbudget
  intro target htarget hupper
  have hQ1 := (tailCollisionCutoff_bounds L hcut.1 hcut.2.1).1
  apply hchoose P S T μ ν (tailDefectBudget a C L) target hE htarget
    hprime hS hT hcard hbudget
  intro j hjlo hjhi p hp
  obtain ⟨hpprime, _, hplog⟩ := mem_primeLogCellSet_iff.mp hp
  have hlog : Real.log (p : ℝ) ≤ Real.log (Q : ℝ) := by
    change Real.log (p : ℝ) ≤ Real.log (tailCollisionCutoff L : ℝ)
    linarith [hplog.2]
  have hpQ : (p : ℝ) ≤ Q :=
    (Real.log_le_log_iff (by exact_mod_cast hpprime.pos)
      (by exact_mod_cast hQ1)).mp hlog
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpQ, hpprime⟩

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

theorem eventual_selected_cell_upper (a C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X target : ℝ, 0 < X → X ≤ Real.exp L →
      target ≤ Real.exp ((105 / 10000 : ℝ) * L) →
      target + 64 * tailDefectBudget a C X + 2 ≤ Real.exp ((11 / 1000 : ℝ) * L) := by
  let D := 256 * C + 256 * Real.log 2 + 128 * Real.log 4 / a + 2
  let K := 1282 + |D|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg D]
  filter_upwards [arithmetic_exponent_absorption (105 / 10000) (11 / 1000) 0 K 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro X target hX hXhi htarget
  have hlogX : Real.log X ≤ L := by
    have h := Real.log_le_log hX hXhi
    rwa [Real.log_exp] at h
  have hlinear : 1280 * L + D ≤ K * L := by
    have hD := le_abs_self D
    have hDL := mul_le_mul_of_nonneg_left hL (abs_nonneg D)
    dsimp [K]
    nlinarith only [hD, hDL, hL]
  have hprod : Real.exp ((105 / 10000 : ℝ) * L) ≤
      K * L * Real.exp ((105 / 10000 : ℝ) * L) :=
    le_mul_of_one_le_left (Real.exp_nonneg _)
      (hL.trans (le_mul_of_one_le_left (by linarith) hK))
  have hbound : target + 64 * tailDefectBudget a C X + 2 ≤
      K * L + K * L * Real.exp ((105 / 10000 : ℝ) * L) := by
    calc
      _ = target + 1280 * Real.log X + D := by dsimp [D, tailDefectBudget]; ring
      _ ≤ Real.exp ((105 / 10000 : ℝ) * L) + 1280 * L + D := by linarith
      _ ≤ _ := by linarith only [hlinear, hprod]
  simp only [pow_one, one_mul, zero_mul, Real.exp_zero] at hrate
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedTailCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected small-cell priors for the actual decomposition -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.selected_tail_cells_at
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℝ, Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp X →
      ∀ target : ℝ, Real.exp ((1 / 100 : ℝ) * L) ≤ target →
        target ≤ Real.exp ((105 / 10000 : ℝ) * L) →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ j : ℕ, target ≤ j ∧ (j : ℝ) ≤ target + 64 * tailDefectBudget a C X + 1 ∧
        (j : ℝ) + 1 ≤ Real.exp ((11 / 1000 : ℝ) * L) ∧
        let Q := (primeLogCellSet 1 0 j ((j : ℝ) + 1) \
          tailCellExceptionalPrimes A B N (summandTailCutoff X) hi (tailCollisionCutoff X)) \ D
        Real.exp (-(2 * L)) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
        0 < (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
        (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * L) ∧
        (∀ p ∈ Q, p.Prime ∧ Real.exp (j : ℝ) < p ∧
          (p : ℝ) ≤ Real.exp ((j : ℝ) + 1) ∧
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
          ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨a, ha, H, hcells⟩ := h.tail_good_prime_cells_at P0 hsize hA hB N hN C hM
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hcells
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventual_tail_cell_window a C H, eventual_selected_cell_upper a C,
    selected_cell_after_finite_deletion,
    ht.eventually (eventually_ge_atTop X₀), eventually_ge_atTop (0 : ℝ)] with L hwindow hrange hmass hlarge hL
  intro X hXlo hXhi hi hhi target htlo hthi D hD
  have hthi' : target ≤ Real.exp ((11 / 1000 : ℝ) * L) := hthi.trans
    (Real.exp_le_exp.mpr (by nlinarith only [hL]))
  obtain ⟨hH, hcut, hsmall⟩ := hwindow X target hXlo hXhi htlo hthi'
  obtain ⟨j, hjlo, hjhi, hjmass, hjbalanced⟩ :=
    hX₀ X (hlarge.trans hXlo) hi hhi target hH hcut
  have hjrange : (j : ℝ) + 1 ≤ Real.exp ((11 / 1000 : ℝ) * L) := by
    have hx : 0 < X := (Real.exp_pos _).trans_le hXlo
    have hr := hrange X target hx hXhi hthi
    linarith
  let S := primeLogCellSet 1 0 j ((j : ℝ) + 1) \
    tailCellExceptionalPrimes A B N (summandTailCutoff X) hi (tailCollisionCutoff X)
  have hjlower : Real.exp ((39 / 10000 : ℝ) * L) ≤ j := by
    apply le_trans _ (htlo.trans hjlo)
    apply Real.exp_le_exp.mpr
    nlinarith only [hL]
  have hjupper : (j : ℝ) ≤ Real.exp (L / 2) := hjhi.trans hsmall
  have hS : S ⊆ primeLogCellSet 1 0 j ((j : ℝ) + 1) := Finset.sdiff_subset
  obtain ⟨hm, hmpos, hnorm⟩ := hmass j S D hjlower hjupper hS hjmass hD
  refine ⟨j, hjlo, hjhi, hjrange, hm, hmpos, hnorm, ?_⟩
  intro p hp
  have hpS := (Finset.mem_sdiff.mp hp).1
  have hpCell := hS hpS
  obtain ⟨hpp, _, hplo, hphi⟩ := mem_primeLogCellSet_iff.mp hpCell
  refine ⟨hpp, ?_, ?_, hjbalanced p hpS⟩
  · exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hpp.pos)).mp hplo
  · exact (Real.log_le_iff_le_exp (by exact_mod_cast hpp.pos)).mp hphi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCompensationCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual top and compensation cell lists -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.selected_compensation_cells_at
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ (k : ℕ), 0 < k →
      ∀ BD Bz : ℝ, 0 ≤ BD → 0 ≤ Bz →
      ∀ᶠ L : ℝ in atTop, ∀ X : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp X →
      ∀ J cb : ℝ, 16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) → 0 ≤ cb → cb ≤ J / 4 →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ (top : ℕ) (centers : List ℕ),
        SelectedSmallTailCell A B N a C L X hi D ((J - cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j)
          centers (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) := by
  obtain ⟨a, ha, hcells⟩ := h.selected_tail_cells_at P0 hsize hA hB N hN C hM
  refine ⟨a, ha, ?_⟩
  intro k hk BD Bz hBD hBz
  filter_upwards [hcells, eventual_protected_cell_target_range,
    eventual_prescribed_compensation_range k hk BD Bz hBD hBz]
    with L hcells htop hcomp
  intro X hXlo hXhi hi hhi J cb hJlo hJhi hcb0 hcb D hD
  have hchoose (target : ℝ) (hlo : Real.exp ((1 / 100 : ℝ) * L) ≤ target)
      (hupper : target ≤ Real.exp ((105 / 10000 : ℝ) * L)) :
      ∃ j, SelectedSmallTailCell A B N a C L X hi D target j :=
    hcells X hXlo hXhi hi hhi target hlo hupper D hD
  obtain ⟨htlo, hthi⟩ := htop J cb hJlo hJhi hcb0 hcb
  obtain ⟨top, htop⟩ := hchoose ((J - cb) / 6) htlo hthi
  have hex : ∀ w ∈ movingCompensationTargets J (movingCompensationGaps k BD Bz L),
      ∃ j, SelectedSmallTailCell A B N a C L X hi D (w / 4) j := by
    intro w hw
    obtain ⟨hlo, hupper⟩ := hcomp J hJlo hJhi w hw
    exact hchoose (w / 4) hlo hupper
  have hlist (ws : List ℝ)
      (hw : ∀ w ∈ ws, ∃ j, SelectedSmallTailCell A B N a C L X hi D (w / 4) j) :
      ∃ cs : List ℕ, List.Forall₂
        (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs ws := by
    induction ws with
    | nil => exact ⟨[], .nil⟩
    | cons w ws ih =>
      obtain ⟨j, hj⟩ := hw w (by simp)
      obtain ⟨cs, hcs⟩ := ih (fun x hx => hw x (by simp [hx]))
      exact ⟨j :: cs, .cons hj hcs⟩
  obtain ⟨centers, hcenters⟩ := hlist _ hex
  exact ⟨top, centers, htop, hcenters⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialTotal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original initial log total for the selected actual cells -/
namespace Ostmann
open scoped BigOperators

theorem selected_compensation_centers_sum_bounds
    {A B : Set ℕ} {N hi : ℕ} {a C L Y : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (h : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets) :
    targets.sum ≤ 4 * (centers.map (fun j : ℕ => (j : ℝ))).sum ∧
      4 * (centers.map (fun j : ℕ => (j : ℝ))).sum ≤
        targets.sum + 4 * centers.length * (64 * tailDefectBudget a C Y + 1) := by
  induction h with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    have hlo := hj.1
    have hhi := hj.2.1
    simp only [List.sum_cons, List.map_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith only [hlo, hhi, ih.1, ih.2]

theorem selected_initial_total_error
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Δ₀ BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd
        (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
          ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers
      (movingCompensationTargets
        (movingProtectedTarget k Y G cd
          (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
            ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)))
        (movingCompensationGaps k BD Bz L))) :
    |2 * (G + cb + cd + 3 * top +
        2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - (Y + Δ₀)| ≤
      (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) := by
  let J := movingProtectedTarget k Y G cd
    (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
      ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L))
  have htotal := moving_protected_and_compensation_total k BD Bz L Y G cd Δ₀
  change 2 * G + 2 * cd + J +
    (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum = Y + Δ₀ at htotal
  have hlen : centers.length = k := by
    have hh := hcenters.length_eq
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hh
  have hsum := selected_compensation_centers_sum_bounds hcenters
  rw [hlen] at hsum
  have hlo := htop.1
  have hhi := htop.2.1
  change (J - 2 * cb) / 6 ≤ (top : ℝ) at hlo
  change (top : ℝ) ≤ (J - 2 * cb) / 6 + 64 * tailDefectBudget a C Y + 1 at hhi
  change (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum ≤ _ ∧ _ at hsum
  have hnonneg : 0 ≤ 2 * (G + cb + cd + 3 * top +
      2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - (Y + Δ₀) := by
    linarith only [hlo, hsum.1, htotal]
  rw [abs_of_nonneg hnonneg]
  nlinarith only [hhi, hsum.2, htotal]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailFourierMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One total Fourier-mass function for the actual tail masks -/
namespace Ostmann
open scoped Classical BigOperators

theorem tailDensityMask_balanced_iff (A : Set ℕ) (N p : ℕ) (hp : 0 < p) :
    ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
      residueDensity (tailDensityMask A N p) ≤ 2 / 3) ↔
    ((p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
      ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  unfold residueDensity
  rw [tailDensityMask_card]
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · rintro ⟨hl, hu⟩
    rw [le_div_iff₀ hp'] at hl
    rw [div_le_iff₀ hp'] at hu
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    constructor
    · apply (le_div_iff₀ hp').mpr
      linarith
    · apply (div_le_iff₀ hp').mpr
      linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Top and compensation cells for the actual initial cutoff centers -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.selected_initial_cells_at
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
      ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ lo G : ℝ,
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      ∀ cb cd : ℤ,
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      let J := movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L)
      ∃ top : ℕ, ∃ centers : List ℕ,
        SelectedSmallTailCell A B N a C L Y hi D ((J - 2 * cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
          centers (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) ∧
        centers.length = k ∧
        |2 * (G + cb + cd + 3 * top +
            2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) -
              (Y + spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L))| ≤
          (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) := by
  obtain ⟨a, ha, hcells⟩ := h.selected_compensation_cells_at P0 hsize hA hB N hN C hM
  refine ⟨a, ha, ?_⟩
  intro k hk Bs BD Bz hBs hBD hBz
  filter_upwards [hcells k (by omega) BD Bz hBD hBz,
    eventual_initial_protected_target k hk Bs BD Bz hBs hBD hBz] with L hcells htarget
  intro Y hYlo hYhi hi hhi lo G hYlo' hYhi' hGlo hGhi cb cd hcb hcd D hD J
  obtain ⟨hJlo, hJhi, hcb0, hcbJ⟩ := htarget cb cd hcb hcd lo G Y hYlo' hYhi' hGlo hGhi
  obtain ⟨top, centers, htop, hcenters⟩ :=
    hcells Y hYlo hYhi hi hhi J (2 * cb) hJlo hJhi hcb0 hcbJ D hD
  refine ⟨top, centers, htop, hcenters, ?_, ?_⟩
  · simpa only [movingCompensationTargets_length, movingCompensationGaps_length]
      using hcenters.length_eq
  · exact selected_initial_total_error k htop hcenters

theorem SelectedSmallTailCell.prior_data
    {A B : Set ℕ} {N hi j : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L Y hi D target j)
    (P : Finset ℕ) (hQP : selectedTailCellPrimes A B N Y hi D j ⊆ P) :
    let Q := selectedTailCellPrimes A B N Y hi D j
    (∑ p : P, primeSubsetPrior P Q p) = 1 ∧
    (∀ p : P, 0 ≤ primeSubsetPrior P Q p ∧
      (p : ℝ) * primeSubsetPrior P Q p ≤ Real.exp (2 * L)) ∧
    (∀ p : P, primeSubsetPrior P Q p ≠ 0 →
      (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3) := by
  intro Q
  obtain ⟨_, _, _, _, hpos, hinv, hsupport⟩ := h
  refine ⟨primeSubsetPrior_mass P Q hQP hpos.ne', ?_, ?_⟩
  · intro p
    refine ⟨primeSubsetPrior_nonneg P Q p, ?_⟩
    by_cases hp : (p : ℕ) ∈ Q
    · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hsupport p hp).1.ne_zero
      calc
        _ ≤ (p : ℝ) * ((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left (primeSubsetPrior_atom P Q p) (Nat.cast_nonneg _)
        _ = (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ := by field_simp
        _ ≤ _ := hinv
    · simp only [primeSubsetPrior, hp, ite_false, if_false, mul_zero]
      positivity
  · intro p hp
    have hs := hsupport p (primeSubsetPrior_support P Q p hp)
    exact (tailDensityMask_balanced_iff A N p hs.1.pos).mpr ⟨hs.2.2.2.1, hs.2.2.2.2⟩

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

theorem mem_initialRegularPrimeRange (L : ℝ) (p : ℕ) (hp : p.Prime)
    (hbound : (p : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) :
    p ∈ initialRegularPrimeRange L := Nat.mem_primesLE.mpr ⟨Nat.le_floor hbound, hp⟩

theorem initial_broad_cell_subset (L α β : ℝ) (hL : 0 ≤ L) (hβ : β ≤ 11 / 1000)
    (D : Finset ℕ) :
    primeLogCellSet 1 0 (Real.exp (α * L)) (Real.exp (β * L)) \ D ⊆
      initialRegularPrimeRange L := by
  intro p hp
  obtain ⟨hprime, _, _, hlog⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
  apply mem_initialRegularPrimeRange L p hprime
  apply ((Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mp hlog).trans
  exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ hL))

theorem SelectedSmallTailCell.subset_initialRegularPrimeRange
    {A B : Set ℕ} {N hi j : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L Y hi D target j) :
    selectedTailCellPrimes A B N Y hi D j ⊆ initialRegularPrimeRange L := by
  intro p hp
  obtain ⟨_, _, hindex, _, _, _, hsupport⟩ := h
  have hs := hsupport p hp
  apply mem_initialRegularPrimeRange L p hs.1
  exact hs.2.2.1.trans (Real.exp_le_exp.mpr hindex)

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

/-- Append every actual top/compensation cell to the two already chosen
cutoff weights. The cells are not conditioned on any new event. -/
theorem initial_selected_cells_balanced_mass
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (P : Finset ℕ) (hsmallP : initialRegularPrimeRange L ⊆ P)
    (b d m : ℕ) (Qb Qd : Finset ℕ) (cb cd : ℝ)
    (hb : Real.exp (-(Real.log 2 + 2) * m) ≤
      ∑ x ∈ balancedTupleSet b (fun _ (p : P) =>
        (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3),
        productPrior (fun _ => primeSubsetPrior P Qb) x *
          initialLogSumWeight (fun p : P => (p : ℕ)) cb x)
    (hd : Real.exp (-(Real.log 2 + 2) * m) ≤
      ∑ x ∈ balancedTupleSet d (fun _ (p : P) =>
        (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3),
        productPrior (fun _ => primeSubsetPrior P Qd) x *
          initialLogSumWeight (fun p : P => (p : ℕ)) cd x) :
    let cells := initialSmallCellList top centers
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y hi D (cells.get i))
    let good := fun p : P => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
      residueDensity (tailDensityMask A N p) ≤ 2 / 3
    Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
      ∑ x ∈ balancedTupleSet (b + (d + cells.length)) (fun _ p => good p),
        productPrior (Fin.append (fun _ : Fin b => primeSubsetPrior P Qb)
          (Fin.append (fun _ : Fin d => primeSubsetPrior P Qd) μc)) x *
            (initialLogSumWeight (fun p : P => (p : ℕ)) cb (fun i => x (i.castAdd (d + cells.length)))) *
              initialLogSumWeight (fun p : P => (p : ℕ)) cd
                (fun i => x ((i.castAdd cells.length).natAdd b)) := by
  intro cells μc good
  have hc (i : Fin cells.length) :=
    initial_selected_cells_valid htop hcenters _ (List.get_mem cells i)
  have hdata (i : Fin cells.length) :=
    (hc i).choose_spec.prior_data P ((hc i).choose_spec.subset_initialRegularPrimeRange.trans hsmallP)
  have he : Fin.append (fun _ : Fin b => good) (Fin.append (fun _ : Fin d => good)
      (fun _ : Fin cells.length => good)) = (fun _ => good) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) j
      · simp only [Fin.append_right, Fin.append_left]
      · simp only [Fin.append_right]
  have hh := initial_balanced_cell_mass_at P b d cells.length m
    (fun _ => primeSubsetPrior P Qb) (fun _ => primeSubsetPrior P Qd) μc
    (fun _ p => good p) (fun _ p => good p) (fun _ p => good p) cb cd hb hd
    (fun i => (hdata i).1) (fun i p hp => (hdata i).2.2 p hp)
  simpa only [he, mul_assoc] using hh

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedInitialNongiantPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the original nongiant priors from the infinite tails -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.constructed_initial_nongiant_priors_oai
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    ∃ a : ℝ, 0 < a ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
      ∀ cutoff : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ lo G : ℝ,
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → initialRegularPrimeRange L ⊆ P →
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      let m := spectatorBulkCount k L
      ∃ Qd : Finset ℕ, ∃ cb cd : ℤ, ∃ top : ℕ, ∃ centers : List ℕ,
        Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
        (∀ p ∈ Qd, cutoff ≤ p ∧
          ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
            residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧
          tailCharacterBias A N p ≤ ε / 2) ∧
        cb ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ ∧
        cd ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ ∧
        SelectedSmallTailCell A B N a C L Y hi D
          ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
          centers (movingCompensationTargets
            (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
            (movingCompensationGaps k BD Bz L)) ∧
        centers.length = k ∧
        |2 * (G + cb + cd + 3 * top + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) -
          (Y + spectatorBaseGap Bs ((k : ℝ) ^ 4) m)| ≤
            (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) ∧
        (∑ p : P, primeSubsetPrior P Qb p) = 1 ∧
        (∑ p : P, primeSubsetPrior P Qd p) = 1 ∧
        (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
          (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) ∧
        let cells := initialSmallCellList top centers
        let μc := fun i : Fin cells.length => primeSubsetPrior P
          (selectedTailCellPrimes A B N Y hi D (cells.get i))
        Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
          ∑ x ∈ balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ (p : P) =>
            (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
              residueDensity (tailDensityMask A N p) ≤ 2 / 3),
            productPrior (Fin.append (fun _ : Fin (m / 2) => primeSubsetPrior P Qb)
              (Fin.append (fun _ : Fin (m / 2) => primeSubsetPrior P Qd) μc)) x *
                initialLogSumWeight (fun p : P => (p : ℕ)) cb
                  (fun i => x (i.castAdd (m / 2 + cells.length))) *
                initialLogSumWeight (fun p : P => (p : ℕ)) cd
                  (fun i => x ((i.castAdd cells.length).natAdd (m / 2))) := by
  classical
  obtain ⟨a, ha, hcells⟩ := h.selected_initial_cells_at P0 hsize hA hB N hN C hM.lower
  refine ⟨a, ha, ?_⟩
  intro k hk Bs BD Bz hBs hBD hBz cutoff ε hε
  filter_upwards [h.initial_broad_prior_centers hBonami P0 H hSiegel sieve hsize hM
    hA hB N hN k cutoff hk ε hε, hcells k hk Bs BD Bz hBs hBD hBz,
    eventually_ge_atTop (0 : ℝ)] with L hbroad hcells hL
  intro Y hYlo hYhi hi hhi lo G hYlo' hYhi' hGlo hGhi D hD P hP hsmallP Qb m
  obtain ⟨Qd, hQd, hmassd, hgood, hpriors⟩ := hbroad Y hYlo hYhi hi hhi D hD
  have hQbP : Qb ⊆ P := (initial_broad_cell_subset L _ _ hL (by norm_num) D).trans hsmallP
  have hQdP : Qd ⊆ P := hQd.trans ((initial_broad_cell_subset L _ _ hL (by norm_num) D).trans hsmallP)
  obtain ⟨hbmass, hdmass, hpoint, cb, hcb, cd, hcd, hb, hd⟩ :=
    hpriors P hP hQbP hQdP
  obtain ⟨top, centers, htop, hcenters, hlen, htotal⟩ :=
    hcells Y hYlo hYhi hi hhi lo G hYlo' hYhi' hGlo hGhi cb cd hcb hcd D hD
  refine ⟨Qd, cb, cd, top, centers, hQd, hmassd, hgood, hcb, hcd,
    htop, hcenters, hlen, htotal, hbmass, hdmass, hpoint, ?_⟩
  exact initial_selected_cells_balanced_mass htop hcenters P hsmallP (m / 2) (m / 2) m Qb Qd cb cd hb hd

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors_oai := @OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors_oai
