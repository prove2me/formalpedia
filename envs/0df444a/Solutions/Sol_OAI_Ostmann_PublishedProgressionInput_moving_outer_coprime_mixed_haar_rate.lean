-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:00:07.049952+00:00
-- url     : https://prove2.me/submissions/563aa1f4-84da-4756-9f43-4dcdf70a6f36

import Mathlib
import Definitions.Def_OAIQ095D008

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryPolynomialSpecialization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual cleared history polynomials with one prime left variable -/

namespace Ostmann

open scoped BigOperators Classical

theorem specializeHistoryVariable_eval {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (x : ℝ) :
    (specializeHistoryVariable a i P).eval x =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P := by
  unfold specializeHistoryVariable
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom x).comp (Polynomial.C.comp (Int.castRingHom ℝ)) =
      Int.castRingHom ℝ := by ext z; simp
  rw [hc]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj, Function.update]

/-- Fixing all the other prime variables cannot increase the degree. The
bound comes from the original monomial support, so cancellation is harmless. -/
theorem specializeHistoryVariable_natDegree {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) :
    (specializeHistoryVariable a i P).natDegree ≤ P.totalDegree := by
  let v : σ → Polynomial ℝ := fun j => if j = i then Polynomial.X else Polynomial.C (a j)
  have hv (j : σ) : (v j).natDegree ≤ 1 := by
    dsimp only [v]
    split_ifs <;> simp
  have hs : specializeHistoryVariable a i P =
      ∑ d ∈ P.support, specializeHistoryVariable a i (MvPolynomial.monomial d (P.coeff d)) := by
    rw [← map_sum]
    exact congrArg (specializeHistoryVariable a i) P.as_sum
  rw [hs]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hp : (d.prod fun j k => v j ^ k).natDegree ≤ d.sum (fun _ k => k) := by
    change (∏ j ∈ d.support, v j ^ d j).natDegree ≤ ∑ j ∈ d.support, d j
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    apply Finset.sum_le_sum
    intro j _
    exact (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (d j) (hv j))).trans_eq (Nat.mul_one _)
  simp only [specializeHistoryVariable, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_monomial, RingHom.comp_apply]
  change ((Polynomial.C ((P.coeff d : ℤ) : ℝ)) * d.prod (fun j k => v j ^ k)).natDegree ≤ _
  calc
    _ ≤ (Polynomial.C ((P.coeff d : ℤ) : ℝ)).natDegree + (d.prod fun j k => v j ^ k).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + d.sum (fun _ k => k) := by simpa only [Polynomial.natDegree_C, zero_add] using hp
    _ ≤ P.totalDegree := by simpa only [zero_add] using MvPolynomial.le_totalDegree hd

theorem normalizedHistoryPolynomial_eval {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (d x : ℝ) :
    (normalizedHistoryPolynomial P a i d).eval x =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P / d := by
  simp only [normalizedHistoryPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    specializeHistoryVariable_eval, div_eq_mul_inv]
  ring

theorem normalizedHistoryPolynomial_natDegree {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (d : ℝ) :
    (normalizedHistoryPolynomial P a i d).natDegree ≤ P.totalDegree := by
  exact (Polynomial.natDegree_mul_le.trans (by
    simpa only [Polynomial.natDegree_C, zero_add] using specializeHistoryVariable_natDegree P a i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ClearedHistoryPivot
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed integer numerators for the recursive pivot substitutions -/

namespace Ostmann

open scoped BigOperators Classical

namespace ClearedHistoryValue

variable {σ : Type*}

theorem degree_prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ) :
    (prod S f).numerator.totalDegree ≤ ∑ i ∈ S, (f i).numerator.totalDegree :=
  MvPolynomial.totalDegree_finsetProd _ _

theorem degree_pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0) :
    (pivot left right v w s hs).numerator.totalDegree ≤
      max left.numerator.totalDegree right.numerator.totalDegree := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact le_max_right _ _)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact le_max_left _ _)

end ClearedHistoryValue

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_WeightedPhaseExtraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting an unweighted interval sum from a weighted phase -/

namespace Ostmann

open scoped BigOperators

/-- Finite Abel summation bounds a weighted sum by the largest prefix sum
and the endpoint-plus-variation of the actual weights. -/
theorem weighted_sum_le_variation (w f : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hprefix : ∀ n ≤ N, ‖∑ j ∈ Finset.range n, f j‖ ≤ M) :
    ‖∑ j ∈ Finset.range N, w j * f j‖ ≤ discreteVariation w N * M := by
  have hab := Finset.sum_range_by_parts w f N
  simp only [smul_eq_mul] at hab
  rw [hab]
  calc
    _ ≤ ‖w (N - 1) * ∑ j ∈ Finset.range N, f j‖ +
        ‖∑ j ∈ Finset.range (N - 1), (w (j + 1) - w j) * ∑ i ∈ Finset.range (j + 1), f i‖ :=
      norm_sub_le _ _
    _ ≤ ‖w (N - 1)‖ * M +
        ∑ j ∈ Finset.range (N - 1), ‖w (j + 1) - w j‖ * M := by
      apply add_le_add
      · rw [Complex.norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix N le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [Complex.norm_mul]
        apply mul_le_mul_of_nonneg_left (hprefix (j + 1) (by
          have hh := Finset.mem_range.mp hj
          omega)) (norm_nonneg _)
    _ = _ := by rw [discreteVariation, ← Finset.sum_mul]; ring

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeIntervalVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted short prime intervals from the published progression input -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem reciprocalPrimeInterval_add (q a : ℕ) (u v w : ℝ) (huv : u ≤ v) (hvw : v ≤ w) :
    reciprocalPrimeInterval q a u v + reciprocalPrimeInterval q a v w =
      reciprocalPrimeInterval q a u w := by
  exact Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor huv) (Nat.floor_le_floor hvw)

theorem primeLogDensity_integral_add (φ χ β u v w : ℝ) (hu : 0 < u) (huv : u ≤ v) (hvw : v ≤ w) :
    (∫ y in Set.Ioc u v, primeLogDensity φ χ β y) +
      (∫ y in Set.Ioc v w, primeLogDensity φ χ β y) =
        ∫ y in Set.Ioc u w, primeLogDensity φ χ β y := by
  rw [← intervalIntegral.integral_of_le huv, ← intervalIntegral.integral_of_le hvw,
    ← intervalIntegral.integral_of_le (huv.trans hvw)]
  exact intervalIntegral.integral_add_adjacent_intervals
    ((continuousOn_primeLogDensity φ χ β hu).intervalIntegrable_of_Icc huv)
    ((continuousOn_primeLogDensity φ χ β (hu.trans_le huv)).intervalIntegrable_of_Icc hvw)

/-- Finite Abel summation turns the uniform interval error into a variation
error for the actual complex weights. There is no factor for the number of
partition intervals. -/
theorem PublishedProgressionInput.weighted_prime_interval_variation
    (P : PublishedProgressionInput) {Q q a : ℕ}
    (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (s : ℕ → ℝ) (hs : Monotone s) (hs0 : 1 ≤ s 0) (N : ℕ) (hshort : s N ≤ s 0 + 1)
    (w : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range N, w j *
      ((reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) -
        ∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y : ℝ) : ℂ)‖ ≤
      discreteVariation w N *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ)))) := by
  let E : ℝ → ℝ := fun t => reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp t) -
    ∫ y in Set.Ioc (s 0) t, selectedPrimeLogDensity P Q q a y
  have hzero : E (s 0) = 0 := by simp [E, reciprocalPrimeInterval]
  have hstep (j : ℕ) :
      reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) -
        (∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y) =
          E (s (j + 1)) - E (s j) := by
    have hp := reciprocalPrimeInterval_add q a (Real.exp (s 0)) (Real.exp (s j))
      (Real.exp (s (j + 1))) (Real.exp_le_exp.mpr (hs (Nat.zero_le _)))
      (Real.exp_le_exp.mpr (hs (Nat.le_succ _)))
    have hi := primeLogDensity_integral_add (Nat.totient q)
      (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
      (pageBeta (pageAtModulus q (selectedPageZero P Q))) (s 0) (s j) (s (j + 1))
      (by linarith) (hs (Nat.zero_le _)) (hs (Nat.le_succ _))
    change (∫ y in Set.Ioc (s 0) (s j), selectedPrimeLogDensity P Q q a y) +
      (∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y) =
        (∫ y in Set.Ioc (s 0) (s (j + 1)), selectedPrimeLogDensity P Q q a y) at hi
    dsimp only [E]
    linarith
  have hprefix (k : ℕ) (hk : k ≤ N) :
      ‖∑ j ∈ Finset.range k, ((E (s (j + 1)) - E (s j) : ℝ) : ℂ)‖ ≤
        18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ))) := by
    rw [← Complex.ofReal_sum, Finset.sum_range_sub (fun j => E (s j)), hzero, sub_zero,
      Complex.norm_real, Real.norm_eq_abs]
    exact P.uniform_log_interval hQ hq hqQ ha hs0 (hs (Nat.zero_le k))
      ((hs hk).trans hshort)
  simp_rw [hstep]
  exact weighted_sum_le_variation w _ N _ hprefix

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

theorem reciprocalPrimeInterval_nonneg (q a : ℕ) (u v : ℝ) :
    0 ≤ reciprocalPrimeInterval q a u v := by
  apply Finset.sum_nonneg
  intro p _
  split <;> positivity

theorem primeLogDensity_abs_le_two (φ χ β : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    |primeLogDensity φ χ β y| ≤ 2 := by
  obtain ⟨hn, hu⟩ := primeLogDensity_bounds φ χ β (by linarith) hχ hβ (by linarith)
  rw [abs_of_nonneg hn]
  apply hu.trans
  exact div_le_self (by norm_num) (by nlinarith : (1 : ℝ) ≤ φ * y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexPrimeWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex smooth weights on actual prime intervals -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexPrimeInterval_add (q a : ℕ) (u v t : ℝ) (w : ℝ → ℂ)
    (huv : u ≤ v) (hvt : v ≤ t) :
    complexPrimeInterval q a u v w + complexPrimeInterval q a v t w =
      complexPrimeInterval q a u t w :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

theorem complexPrimeInterval_freeze (q a : ℕ) (s t : ℝ) (w : ℝ → ℂ) (c : ℂ) (η : ℝ)
    (hw : ∀ y ∈ Set.Ioc s t, ‖w y - c‖ ≤ η) :
    ‖complexPrimeInterval q a s t w -
      c * (reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) : ℂ)‖ ≤
        η * reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) := by
  have heq : complexPrimeInterval q a s t w -
      c * (reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) : ℂ) =
      ∑ p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
        if p.Prime ∧ Nat.ModEq q p a then (w (Real.log p) - c) * ((p : ℝ)⁻¹ : ℂ) else 0 := by
    unfold complexPrimeInterval reciprocalPrimeInterval
    rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split <;> simp_all [sub_mul]
  rw [heq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
        η * (if p.Prime ∧ Nat.ModEq q p a then (p : ℝ)⁻¹ else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases h : p.Prime ∧ Nat.ModEq q p a
      · rw [ite_eq_left h, ite_eq_left h, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg p)]
        exact mul_le_mul_of_nonneg_right (hw _ (log_mem_of_mem_exp_interval hp)) (by positivity)
      · simp [h]
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Freezing a continuous complex weight costs its oscillation times the
length of the log interval. In particular the cost is additive over meshes. -/
theorem complex_density_integral_freeze (φ χ β s t : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) (hs : 1 ≤ s) (hst : s ≤ t)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc s t)) (c : ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc s t, ‖w y - c‖ ≤ η) :
    ‖(∫ y in Set.Ioc s t, w y * (primeLogDensity φ χ β y : ℂ)) -
      c * (∫ y in Set.Ioc s t, primeLogDensity φ χ β y : ℝ)‖ ≤ 2 * η * (t - s) := by
  have hc := continuousOn_primeLogDensity φ χ β (t := t) (by linarith : 0 < s)
  have hiw : IntegrableOn (fun y => w y * (primeLogDensity φ χ β y : ℂ)) (Set.Ioc s t) :=
    (hwc.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hic : IntegrableOn (fun y => c * (primeLogDensity φ χ β y : ℂ)) (Set.Ioc s t) :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have heq : (∫ y in Set.Ioc s t, w y * (primeLogDensity φ χ β y : ℂ)) -
      c * (∫ y in Set.Ioc s t, primeLogDensity φ χ β y : ℝ) =
      ∫ y in Set.Ioc s t, (w y - c) * (primeLogDensity φ χ β y : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul, ← integral_sub hiw hic]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y _
    ring
  rw [heq]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := 2 * η)
    (f := fun y => (w y - c) * (primeLogDensity φ χ β y : ℂ))
    (fun y hy => by
      have hy' := (Set.uIoc_of_le hst) ▸ hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hw y hy')
        (primeLogDensity_abs_le_two φ χ β hφ hχ hβ (hs.trans hy'.1.le))
        (abs_nonneg _) hη).trans_eq (mul_comm η 2))
  rwa [intervalIntegral.integral_of_le hst, abs_of_nonneg (sub_nonneg.mpr hst)] at hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimePartitionVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partition approximation without a partition-count loss -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexPrimeInterval_partition (q a : ℕ) (s : ℕ → ℝ) (hs : Monotone s)
    (w : ℝ → ℂ) (N : ℕ) :
    (∑ j ∈ Finset.range N, complexPrimeInterval q a (s j) (s (j + 1)) w) =
      complexPrimeInterval q a (s 0) (s N) w := by
  induction N with
  | zero => simp [complexPrimeInterval]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact complexPrimeInterval_add q a _ _ _ w (hs (Nat.zero_le _)) (hs (Nat.le_succ _))

theorem reciprocalPrimeInterval_partition (q a : ℕ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) :
    (∑ j ∈ Finset.range N, reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1)))) =
      reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp (s N)) := by
  induction N with
  | zero => simp [reciprocalPrimeInterval]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact reciprocalPrimeInterval_add q a _ _ _
        (Real.exp_le_exp.mpr (hs (Nat.zero_le _))) (Real.exp_le_exp.mpr (hs (Nat.le_succ _)))

theorem integral_Ioc_partition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) (f : ℝ → E)
    (hf : ContinuousOn f (Set.Icc (s 0) (s N))) :
    (∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)), f y) =
      ∫ y in Set.Ioc (s 0) (s N), f y := by
  have heq (j : ℕ) : (∫ y in Set.Ioc (s j) (s (j + 1)), f y) =
      ∫ y in (s j)..(s (j + 1)), f y :=
    (intervalIntegral.integral_of_le (hs (Nat.le_succ _))).symm
  simp_rw [heq]
  rw [← intervalIntegral.integral_of_le (hs (Nat.zero_le _))]
  apply intervalIntegral.sum_integral_adjacent_intervals
  intro j hj
  apply (hf.mono ?_).intervalIntegrable_of_Icc (hs (Nat.le_succ _))
  intro y hy
  exact ⟨(hs (Nat.zero_le _)).trans hy.1, hy.2.trans (hs (by omega))⟩

/-- The oscillation error is proportional to total mass and total interval
length. The progression error is proportional to variation, with neither
error multiplied by the number of intervals. -/
theorem PublishedProgressionInput.prime_partition_variation (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (s : ℕ → ℝ) (hs : Monotone s) (hs0 : 1 ≤ s 0) (N : ℕ) (hshort : s N ≤ s 0 + 1)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc (s 0) (s N))) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖w y - w (s j)‖ ≤ η) :
    ‖complexPrimeInterval q a (s 0) (s N) w -
        ∫ y in Set.Ioc (s 0) (s N), w y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      discreteVariation (fun j => w (s j)) N *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ)))) +
      η * (reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp (s N)) +
        2 * (s N - s 0)) := by
  let A (j : ℕ) := complexPrimeInterval q a (s j) (s (j + 1)) w
  let B (j : ℕ) := w (s j) * (reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) : ℂ)
  let C (j : ℕ) := w (s j) * (∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y : ℝ)
  let D (j : ℕ) := ∫ y in Set.Ioc (s j) (s (j + 1)), w y * (selectedPrimeLogDensity P Q q a y : ℂ)
  have hρ : ContinuousOn (selectedPrimeLogDensity P Q q a) (Set.Icc (s 0) (s N)) :=
    continuousOn_primeLogDensity _ _ _ (by linarith)
  have hA : ‖∑ j ∈ Finset.range N, (A j - B j)‖ ≤
      η * reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp (s N)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, η * reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) := by
        apply Finset.sum_le_sum
        intro j hj
        exact complexPrimeInterval_freeze q a _ _ w _ η (hw j (Finset.mem_range.mp hj))
      _ = _ := by rw [← Finset.mul_sum, reciprocalPrimeInterval_partition q a s hs N]
  have hD : ‖∑ j ∈ Finset.range N, (C j - D j)‖ ≤ 2 * η * (s N - s 0) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, 2 * η * (s (j + 1) - s j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_sub_rev]
        apply complex_density_integral_freeze _ _ _ _ _
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q))
          (pageCoefficient_abs_le_one _ _) (pageBeta_le_one _)
          (hs0.trans (hs (Nat.zero_le _))) (hs (Nat.le_succ _)) w
        · apply hwc.mono
          intro y hy
          exact ⟨(hs (Nat.zero_le _)).trans hy.1,
            hy.2.trans (hs (by have := Finset.mem_range.mp hj; omega))⟩
        · exact hη
        · exact hw j (Finset.mem_range.mp hj)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub s]
  have hBC : ‖∑ j ∈ Finset.range N, (B j - C j)‖ ≤
      discreteVariation (fun j => w (s j)) N *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ)))) := by
    simpa only [B, C, ← mul_sub, ← Complex.ofReal_sub] using
      P.weighted_prime_interval_variation hQ hq hqQ ha s hs hs0 N hshort (fun j => w (s j))
  have hid : complexPrimeInterval q a (s 0) (s N) w -
        (∫ y in Set.Ioc (s 0) (s N), w y * (selectedPrimeLogDensity P Q q a y : ℂ)) =
      (∑ j ∈ Finset.range N, (A j - B j)) +
        (∑ j ∈ Finset.range N, (B j - C j)) + (∑ j ∈ Finset.range N, (C j - D j)) := by
    have hcont : ContinuousOn (fun y => w y * (selectedPrimeLogDensity P Q q a y : ℂ))
        (Set.Icc (s 0) (s N)) := hwc.mul (Complex.continuous_ofReal.comp_continuousOn hρ)
    rw [← complexPrimeInterval_partition q a s hs w N,
      ← integral_Ioc_partition s hs N (fun y => w y * (selectedPrimeLogDensity P Q q a y : ℂ)) hcont]
    simp only [Finset.sum_sub_distrib, A, D]
    ring
  rw [hid]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (by linarith [add_le_add (add_le_add hA hBC) hD])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ContinuousIntervalMesh
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite meshes for the continuous factors in prime comparison -/

namespace Ostmann

/-- Mesh fineness is arbitrary and has no arithmetic cost: the progression
comparison uses total variation instead of counting the subintervals. -/
theorem continuous_interval_mesh (u v : ℝ) (huv : u ≤ v) (w : ℝ → ℂ)
    (hw : ContinuousOn w (Set.Icc u v)) (η : ℝ) (hη : 0 < η) :
    ∃ (s : ℕ → ℝ) (N : ℕ), 0 < N ∧ Monotone s ∧ s 0 = u ∧ s N = v ∧
      ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖w y - w (s j)‖ ≤ η := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hw) η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((v - u) / δ)
  let N := n + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hmesh : (v - u) / N < δ := by
    apply (div_lt_iff₀ hN).mpr
    have hh : (v - u) / δ < (N : ℝ) := hn.trans (by dsimp [N]; push_cast; linarith)
    have := (div_lt_iff₀ hδ).mp hh
    nlinarith
  let s : ℕ → ℝ := fun j => u + (v - u) * j / N
  have hs : Monotone s := by
    intro i j hij
    dsimp [s]
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hij)
      (sub_nonneg.mpr huv)) hN.le
  have hs0 : s 0 = u := by simp [s]
  have hsN : s N = v := by dsimp [s]; field_simp; ring
  refine ⟨s, N, by dsimp [N]; omega, hs, hs0, hsN, ?_⟩
  intro j hj y hy
  have hsju : u ≤ s j := by rw [← hs0]; exact hs (Nat.zero_le _)
  have hsjv : s (j + 1) ≤ v := by rw [← hsN]; exact hs (by omega)
  have hsj : s j ∈ Set.Icc u v := ⟨hsju, (hs (Nat.le_succ _)).trans hsjv⟩
  have hyuv : y ∈ Set.Icc u v := ⟨hsju.trans hy.1.le, hy.2.trans hsjv⟩
  have hwidth : s (j + 1) - s j = (v - u) / N := by dsimp [s]; push_cast; ring
  have hdist : dist y (s j) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1.le)]
    calc
      y - s j ≤ s (j + 1) - s j := sub_le_sub_right hy.2 _
      _ < δ := hwidth ▸ hmesh
  simpa only [dist_eq_norm] using (hmod y hyuv (s j) hsj hdist).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_IntegerIntervalDistribution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary interval distribution for the external integer giant -/

namespace Ostmann

open scoped Classical
open MeasureTheory

theorem integer_interval_residue_error (lo hi q a : ℕ) (hlo : lo ≤ hi) (hq : 0 < q) :
    |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℝ) -
      ((hi : ℝ) - lo) / q| ≤ 1 := by
  let A : ℚ := ((lo : ℚ) - a) / q
  let B : ℚ := ((hi : ℚ) - a) / q
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (by exact_mod_cast hlo : (lo : ℚ) ≤ hi) a) hq'.le
  have hf := Int.floor_mono hAB
  have hcard := Nat.Ioc_filter_modEq_card lo hi hq a
  have hcast : (((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) =
      ((⌊B⌋ : ℤ) : ℚ) - ((⌊A⌋ : ℤ) : ℚ) := by
    rw [max_eq_left (sub_nonneg.mpr hf)] at hcard
    exact_mod_cast hcard
  have hA := Int.floor_le A
  have hA' := Int.lt_floor_add_one A
  have hB := Int.floor_le B
  have hB' := Int.lt_floor_add_one B
  have hrat : |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| ≤ 1 := by
    rw [hcast]
    have hid : ((hi : ℚ) - lo) / q = B - A := by dsimp [A, B]; ring
    rw [hid, abs_le]
    constructor <;> linarith
  have hr : ((|(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr hrat
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using hr

theorem real_interval_residue_error (q a : ℕ) (hq : 0 < q) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) :
    |(((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ) -
      (v - u) / q| ≤ 2 := by
  have h := integer_interval_residue_error ⌊u⌋₊ ⌊v⌋₊ q a (Nat.floor_mono huv) hq
  have hv : 0 ≤ v := hu.trans huv
  have hu0 := Nat.floor_le hu
  have hu1 := Nat.lt_floor_add_one u
  have hv0 := Nat.floor_le hv
  have hv1 := Nat.lt_floor_add_one v
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : |(((⌊v⌋₊ : ℕ) : ℝ) - ⌊u⌋₊) / q - (v - u) / q| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hq0, div_le_one hq0, abs_le]
    constructor <;> linarith
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ)
    ((((⌊v⌋₊ : ℕ) : ℝ) - ⌊u⌋₊) / q) ((v - u) / q)
  simp only [Real.norm_eq_abs] at ht
  linarith

/-- The logarithmic integer coordinate has main density `exp(t)/q`.
Multiplication by its original normalization costs exactly the same factor
on the uniform absolute error. -/
theorem integer_log_interval_residue_error (q a : ℕ) (hq : 0 < q)
    (s t G : ℝ) (hst : s ≤ t) :
    |Real.exp (-G) *
      (((Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ) -
      Real.exp (-G) * ((Real.exp t - Real.exp s) / q)| ≤ 2 * Real.exp (-G) := by
  rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left
    (real_interval_residue_error q a hq (Real.exp_pos s).le (Real.exp_le_exp.mpr hst))
    (Real.exp_pos (-G)).le).trans_eq (mul_comm _ _)

theorem integerLogDensity_integral (q : ℕ) (s t G : ℝ) (hst : s ≤ t) :
    (∫ y in Set.Ioc s t, integerLogDensity q G y) =
      Real.exp (-G) * ((Real.exp t - Real.exp s) / q) := by
  calc
    _ = ∫ y in Set.Ioc s t, (Real.exp (-G) / q) * Real.exp y := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y _
      dsimp [integerLogDensity]
      rw [Real.exp_sub, Real.exp_neg]
      ring
    _ = (Real.exp (-G) / q) * (∫ y in Set.Ioc s t, Real.exp y) := integral_const_mul _ _
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hst, integral_exp]
      ring

/-- The external integer coordinate has the claimed real log density,
with an explicit absolute error uniform in every residue class. -/
theorem integer_log_density_error (q a : ℕ) (hq : 0 < q)
    (s t G : ℝ) (hst : s ≤ t) :
    |Real.exp (-G) *
      (((Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ) -
      ∫ y in Set.Ioc s t, integerLogDensity q G y| ≤ 2 * Real.exp (-G) := by
  rw [integerLogDensity_integral q s t G hst]
  exact integer_log_interval_residue_error q a hq s t G hst

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedIntegerIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutoff-weighted distribution of the external integer coordinate -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem integerLogCellMass_eq (q a : ℕ) (s t G : ℝ) :
    integerLogCellMass q a s t G = Real.exp (-G) *
      (((Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ) := by
  unfold integerLogCellMass integerResidueAtom
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem integerLogCellMass_error (q a : ℕ) (hq : 0 < q)
    (s t G : ℝ) (hst : s ≤ t) :
    |integerLogCellMass q a s t G - ∫ y in Set.Ioc s t, integerLogDensity q G y| ≤
      2 * Real.exp (-G) := by
  rw [integerLogCellMass_eq]
  exact integer_log_density_error q a hq s t G hst

theorem integerLogDensity_abs_le (q : ℕ) (hq : 0 < q) (G : ℝ) {y t : ℝ} (hyt : y ≤ t) :
    |integerLogDensity q G y| ≤ Real.exp (t - G) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  unfold integerLogDensity
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_self (Real.exp_pos _).le hq1).trans
    (Real.exp_le_exp.mpr (sub_le_sub_right hyt G))

theorem integerLogDensity_integral_abs_le (q : ℕ) (hq : 0 < q) (s t G : ℝ)
    (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |∫ y in Set.Ioc s t, integerLogDensity q G y| ≤ Real.exp (t - G) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := Real.exp (t - G)) (f := integerLogDensity q G)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      exact integerLogDensity_abs_le q hq G (((Set.uIoc_of_le hst) ▸ hy).2))
  rw [intervalIntegral.integral_of_le hst, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at h
  exact h.trans (by nlinarith [Real.exp_pos (t - G)])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerIntervalVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Abel variation for the original external integer measure -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexIntegerInterval_add (q a : ℕ) (u v t G : ℝ) (w : ℝ → ℂ)
    (huv : u ≤ v) (hvt : v ≤ t) :
    complexIntegerInterval q a u v G w + complexIntegerInterval q a v t G w =
      complexIntegerInterval q a u t G w :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

theorem integerLogCellMass_add (q a : ℕ) (u v t G : ℝ) (huv : u ≤ v) (hvt : v ≤ t) :
    integerLogCellMass q a u v G + integerLogCellMass q a v t G =
      integerLogCellMass q a u t G :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

theorem integerResidueAtom_nonneg (q a : ℕ) (G : ℝ) (n : ℕ) :
    0 ≤ integerResidueAtom q a G n := by
  unfold integerResidueAtom
  split_ifs <;> positivity

theorem integerLogCellMass_nonneg (q a : ℕ) (u v G : ℝ) :
    0 ≤ integerLogCellMass q a u v G :=
  Finset.sum_nonneg (fun _ _ => integerResidueAtom_nonneg _ _ _ _)

theorem continuous_integerLogDensity (q : ℕ) (G : ℝ) : Continuous (integerLogDensity q G) :=
  (Real.continuous_exp.comp (continuous_id.sub continuous_const)).div_const q

theorem complexIntegerInterval_freeze (q a : ℕ) (u v G : ℝ)
    (w : ℝ → ℂ) (c : ℂ) (η : ℝ)
    (hw : ∀ y ∈ Set.Ioc u v, ‖w y - c‖ ≤ η) :
    ‖complexIntegerInterval q a u v G w - c * (integerLogCellMass q a u v G : ℂ)‖ ≤
      η * integerLogCellMass q a u v G := by
  have heq : complexIntegerInterval q a u v G w - c * (integerLogCellMass q a u v G : ℂ) =
      ∑ n ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
        (w (Real.log n) - c) * (integerResidueAtom q a G n : ℂ) := by
    unfold complexIntegerInterval integerLogCellMass
    rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, η * integerResidueAtom q a G n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integerResidueAtom_nonneg q a G n)]
      exact mul_le_mul_of_nonneg_right (hw _ (log_mem_of_mem_exp_interval hn))
        (integerResidueAtom_nonneg q a G n)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem integerLogCellMass_partition (q a : ℕ) (G : ℝ) (s : ℕ → ℝ)
    (hs : Monotone s) (N : ℕ) :
    (∑ j ∈ Finset.range N, integerLogCellMass q a (s j) (s (j + 1)) G) =
      integerLogCellMass q a (s 0) (s N) G := by
  induction N with
  | zero => simp [integerLogCellMass]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    exact integerLogCellMass_add q a _ _ _ G (hs (Nat.zero_le _)) (hs (Nat.le_succ _))

theorem complexIntegerInterval_partition (q a : ℕ) (G : ℝ) (s : ℕ → ℝ)
    (hs : Monotone s) (w : ℝ → ℂ) (N : ℕ) :
    (∑ j ∈ Finset.range N, complexIntegerInterval q a (s j) (s (j + 1)) G w) =
      complexIntegerInterval q a (s 0) (s N) G w := by
  induction N with
  | zero => simp [complexIntegerInterval]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    exact complexIntegerInterval_add q a _ _ _ G w (hs (Nat.zero_le _)) (hs (Nat.le_succ _))

/-- The integer progression discrepancy pays total variation rather than
the number of intervals. The normalization remains the original exp(-G). -/
theorem weighted_integer_interval_variation (q a : ℕ) (hq : 0 < q) (G : ℝ)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) (w : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range N, w j *
      ((integerLogCellMass q a (s j) (s (j + 1)) G -
        ∫ y in Set.Ioc (s j) (s (j + 1)), integerLogDensity q G y : ℝ) : ℂ)‖ ≤
      discreteVariation w N * (2 * Real.exp (-G)) := by
  apply weighted_sum_le_variation
  intro k _
  rw [← Complex.ofReal_sum, Finset.sum_sub_distrib, integerLogCellMass_partition q a G s hs k,
    integral_Ioc_partition s hs k _ (continuous_integerLogDensity q G).continuousOn,
    Complex.norm_real, Real.norm_eq_abs]
  exact integerLogCellMass_error q a hq _ _ G (hs (Nat.zero_le _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ContinuousIntegerComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous weights under the original external integer law -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complex_integer_density_freeze (q : ℕ) (hq : 0 < q) (u v G : ℝ) (huv : u ≤ v)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (c : ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc u v, ‖w y - c‖ ≤ η) :
    ‖(∫ y in Set.Ioc u v, w y * (integerLogDensity q G y : ℂ)) -
      c * (∫ y in Set.Ioc u v, integerLogDensity q G y : ℝ)‖ ≤
        η * Real.exp (v - G) * (v - u) := by
  have hc := (continuous_integerLogDensity q G).continuousOn (s := Set.Icc u v)
  have hiw : IntegrableOn (fun y => w y * (integerLogDensity q G y : ℂ)) (Set.Ioc u v) :=
    (hwc.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hic : IntegrableOn (fun y => c * (integerLogDensity q G y : ℂ)) (Set.Ioc u v) :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have heq : (∫ y in Set.Ioc u v, w y * (integerLogDensity q G y : ℂ)) -
      c * (∫ y in Set.Ioc u v, integerLogDensity q G y : ℝ) =
      ∫ y in Set.Ioc u v, (w y - c) * (integerLogDensity q G y : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul, ← integral_sub hiw hic]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y _
    ring
  rw [heq]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := η * Real.exp (v - G))
    (f := fun y => (w y - c) * (integerLogDensity q G y : ℂ))
    (fun y hy => by
      have hy' := (Set.uIoc_of_le huv) ▸ hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hw y hy') (integerLogDensity_abs_le q hq G hy'.2) (abs_nonneg _) hη)
  rwa [intervalIntegral.integral_of_le huv, abs_of_nonneg (sub_nonneg.mpr huv)] at hi

/-- A partition only incurs oscillation times total mass and interval length.
Its progression error is bounded by variation independently of the mesh. -/
theorem integer_partition_variation (q a : ℕ) (hq : 0 < q) (G : ℝ)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc (s 0) (s N))) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖w y - w (s j)‖ ≤ η) :
    ‖complexIntegerInterval q a (s 0) (s N) G w -
        ∫ y in Set.Ioc (s 0) (s N), w y * (integerLogDensity q G y : ℂ)‖ ≤
      discreteVariation (fun j => w (s j)) N * (2 * Real.exp (-G)) +
      η * (integerLogCellMass q a (s 0) (s N) G + Real.exp (s N - G) * (s N - s 0)) := by
  let A (j : ℕ) := complexIntegerInterval q a (s j) (s (j + 1)) G w
  let B (j : ℕ) := w (s j) * (integerLogCellMass q a (s j) (s (j + 1)) G : ℂ)
  let C (j : ℕ) := w (s j) * (∫ y in Set.Ioc (s j) (s (j + 1)), integerLogDensity q G y : ℝ)
  let D (j : ℕ) := ∫ y in Set.Ioc (s j) (s (j + 1)), w y * (integerLogDensity q G y : ℂ)
  have hA : ‖∑ j ∈ Finset.range N, (A j - B j)‖ ≤
      η * integerLogCellMass q a (s 0) (s N) G := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, η * integerLogCellMass q a (s j) (s (j + 1)) G := by
        apply Finset.sum_le_sum
        intro j hj
        exact complexIntegerInterval_freeze q a _ _ G w _ η (hw j (Finset.mem_range.mp hj))
      _ = _ := by rw [← Finset.mul_sum, integerLogCellMass_partition q a G s hs N]
  have hD : ‖∑ j ∈ Finset.range N, (C j - D j)‖ ≤
      η * Real.exp (s N - G) * (s N - s 0) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, η * Real.exp (s N - G) * (s (j + 1) - s j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_sub_rev]
        apply (complex_integer_density_freeze q hq _ _ G (hs (Nat.le_succ _)) w
          (hwc.mono (by
            intro y hy
            exact ⟨(hs (Nat.zero_le _)).trans hy.1,
              hy.2.trans (hs (by have := Finset.mem_range.mp hj; omega))⟩))
          _ η hη (hw j (Finset.mem_range.mp hj))).trans
        apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr (hs (Nat.le_succ _)))
        apply mul_le_mul_of_nonneg_left _ hη
        apply Real.exp_le_exp.mpr
        exact sub_le_sub_right (hs (by have := Finset.mem_range.mp hj; omega)) G
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub s]
  have hBC : ‖∑ j ∈ Finset.range N, (B j - C j)‖ ≤
      discreteVariation (fun j => w (s j)) N * (2 * Real.exp (-G)) := by
    simpa only [B, C, ← mul_sub, ← Complex.ofReal_sub] using
      weighted_integer_interval_variation q a hq G s hs N (fun j => w (s j))
  have hid : complexIntegerInterval q a (s 0) (s N) G w -
        (∫ y in Set.Ioc (s 0) (s N), w y * (integerLogDensity q G y : ℂ)) =
      (∑ j ∈ Finset.range N, (A j - B j)) +
        (∑ j ∈ Finset.range N, (B j - C j)) + (∑ j ∈ Finset.range N, (C j - D j)) := by
    have hcont : ContinuousOn (fun y => w y * (integerLogDensity q G y : ℂ))
        (Set.Icc (s 0) (s N)) :=
      hwc.mul (Complex.continuous_ofReal.comp_continuousOn (continuous_integerLogDensity q G).continuousOn)
    rw [← complexIntegerInterval_partition q a G s hs w N,
      ← integral_Ioc_partition s hs N (fun y => w y * (integerLogDensity q G y : ℂ)) hcont]
    simp only [Finset.sum_sub_distrib, A, D]
    ring
  rw [hid]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (by linarith [add_le_add (add_le_add hA hBC) hD])

/-- The external integer comparison keeps the original normalization and
requires no fixed mesh or partition-count loss. -/
theorem continuous_integer_comparison (q a : ℕ) (hq : 0 < q) (u v G : ℝ) (huv : u ≤ v)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V : ℝ)
    (hV : ∀ (s : ℕ → ℝ), Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V) :
    ‖complexIntegerInterval q a u v G w -
        ∫ y in Set.Ioc u v, w y * (integerLogDensity q G y : ℂ)‖ ≤
      V * (2 * Real.exp (-G)) := by
  let M := integerLogCellMass q a u v G + Real.exp (v - G) * (v - u)
  have hM : 0 ≤ M := add_nonneg (integerLogCellMass_nonneg q a u v G)
    (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr huv))
  have hM1 : 0 < M + 1 := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε / (M + 1)
  have hη : 0 < η := div_pos hε hM1
  obtain ⟨s, N, _hN, hs, hs0, hsN, hosc⟩ := continuous_interval_mesh u v huv w hwc η hη
  have hc : ContinuousOn w (Set.Icc (s 0) (s N)) := by simpa only [hs0, hsN] using hwc
  have hb := integer_partition_variation q a hq G s hs N w hc η hη.le hosc
  rw [hs0, hsN] at hb
  apply hb.trans
  have hvar := mul_le_mul_of_nonneg_right (hV s hs N hs0 hsN) (by positivity : 0 ≤ 2 * Real.exp (-G))
  have hsmall : η * M ≤ ε := by
    have hid : η * (M + 1) = ε := by dsimp [η]; field_simp
    nlinarith
  exact add_le_add hvar hsmall

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_OpenCellIntegerComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Open integer cells retain their endpoint atoms -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

theorem complexIntegerInterval_open_cell_bound (q a : ℕ) (u v G : ℝ)
    (W w : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexIntegerInterval q a u v G W - complexIntegerInterval q a u v G w‖ ≤
      B * Real.exp (-G) := by
  let T := Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊
  let S : Finset ℕ := {⌊Real.exp v⌋₊}
  have hC : 0 ≤ B * Real.exp (-G) := mul_nonneg hB (Real.exp_pos _).le
  have hatom (n : ℕ) : ‖(integerResidueAtom q a G n : ℂ)‖ ≤ Real.exp (-G) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integerResidueAtom_nonneg q a G n)]
    unfold integerResidueAtom
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hpoint (n : ℕ) (hn : n ∈ T) :
      ‖(W (Real.log n) - w (Real.log n)) * (integerResidueAtom q a G n : ℂ)‖ ≤
        if n ∈ S then B * Real.exp (-G) else 0 := by
    by_cases hS : n ∈ S
    · rw [ite_eq_left hS, norm_mul]
      exact mul_le_mul (hbound _ (log_mem_of_mem_exp_interval hn)) (hatom n) (norm_nonneg _) hB
    · rw [ite_eq_right hS]
      have hlog := log_mem_of_mem_exp_interval hn
      have hn0 : (0 : ℝ) < n := by
        have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
        exact_mod_cast this
      have hne : Real.log n ≠ v := by
        intro hv
        apply hS
        simp only [S, Finset.mem_singleton]
        rw [← hv, Real.exp_log hn0, Nat.floor_natCast]
      rw [heq _ ⟨hlog.1, lt_of_le_of_ne hlog.2 hne⟩, sub_self, zero_mul, norm_zero]
  have he : complexIntegerInterval q a u v G W - complexIntegerInterval q a u v G w =
      ∑ n ∈ T, (W (Real.log n) - w (Real.log n)) * (integerResidueAtom q a G n : ℂ) := by
    simp only [complexIntegerInterval, ← Finset.sum_sub_distrib, T, sub_mul]
  rw [he]
  calc
    _ ≤ ∑ n ∈ T, ‖(W (Real.log n) - w (Real.log n)) * (integerResidueAtom q a G n : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ T, if n ∈ S then B * Real.exp (-G) else 0 := Finset.sum_le_sum hpoint
    _ = ((T.filter (· ∈ S)).card : ℝ) * (B * Real.exp (-G)) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (S.card : ℝ) * (B * Real.exp (-G)) := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_card (show T.filter (· ∈ S) ⊆ S from
        fun _ h => (Finset.mem_filter.mp h).2)
    _ = _ := by simp [S]

theorem open_cell_integer_comparison (q a : ℕ) (hq : 0 < q) (u v G : ℝ) (huv : u ≤ v)
    (W w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V B : ℝ)
    (hV : ∀ s : ℕ → ℝ, Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V)
    (hB : 0 ≤ B) (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexIntegerInterval q a u v G W -
      ∫ y in Set.Ioc u v, w y * (integerLogDensity q G y : ℂ)‖ ≤
        V * (2 * Real.exp (-G)) + B * Real.exp (-G) := by
  have h1 := complexIntegerInterval_open_cell_bound q a u v G W w B hB hbound heq
  have h2 := continuous_integer_comparison q a hq u v G huv w hwc V hV
  exact (norm_sub_le_norm_sub_add_norm_sub _ (complexIntegerInterval q a u v G w) _).trans
    (by linarith)

theorem piecewise_integer_comparison (q a : ℕ) (hq : 0 < q) (G : ℝ)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (W : ℝ → ℂ) (w : ℕ → ℝ → ℂ) (V B : ℕ → ℝ)
    (hwc : ∀ j < N, ContinuousOn (w j) (Set.Icc (s j) (s (j + 1))))
    (hV : ∀ j < N, ∀ r : ℕ → ℝ, Monotone r → ∀ M,
      r 0 = s j → r M = s (j + 1) → discreteVariation (fun k => w j (r k)) M ≤ V j)
    (hB : ∀ j < N, 0 ≤ B j)
    (hbound : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖W y - w j y‖ ≤ B j)
    (heq : ∀ j < N, ∀ y ∈ Set.Ioo (s j) (s (j + 1)), W y = w j y) :
    ‖complexIntegerInterval q a (s 0) (s N) G W -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        w j y * (integerLogDensity q G y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N, (V j * (2 * Real.exp (-G)) + B j * Real.exp (-G)) := by
  rw [← complexIntegerInterval_partition q a G s hs W N, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  exact open_cell_integer_comparison q a hq _ _ G (hs (Nat.le_succ _))
    W (w j) (hwc j hjN) (V j) (B j) (hV j hjN) (hB j hjN) (hbound j hjN) (heq j hjN)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MonotoneWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variation of the smooth factors on monotone argument intervals -/

namespace Ostmann

open scoped BigOperators

theorem clipRealInterval_monotone (lo hi : ℝ) : Monotone (clipRealInterval lo hi) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

/-- Only bounds on the actual compact argument interval are needed. -/
theorem discreteVariation_comp_monotoneOn (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Set.Icc lo hi, ‖Φ x‖ ≤ B)
    (hlip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hrange : ∀ j ≤ N - 1, u j ∈ Set.Icc lo hi)
    (hmono : ∀ j < N - 1, u j ≤ u (j + 1)) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hs : (∑ j ∈ Finset.range (N - 1), ‖Φ (u (j + 1)) - Φ (u j)‖) ≤
      D * (u (N - 1) - u 0) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N - 1), D * (u (j + 1) - u j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simpa only [abs_of_nonneg (sub_nonneg.mpr (hmono j hj'))] using
          hlip (u (j + 1)) (hrange (j + 1) (by omega)) (u j) (hrange j (by omega))
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]
  have hw : u (N - 1) - u 0 ≤ hi - lo := by
    have h1 := (hrange (N - 1) le_rfl).2
    have h0 := (hrange 0 (Nat.zero_le _)).1
    linarith
  exact add_le_add (hbound _ (hrange _ le_rfl))
    (hs.trans (mul_le_mul_of_nonneg_left hw hD))

theorem discreteVariation_comp_antitoneOn (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Set.Icc lo hi, ‖Φ x‖ ≤ B)
    (hlip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hrange : ∀ j ≤ N - 1, u j ∈ Set.Icc lo hi)
    (hanti : ∀ j < N - 1, u (j + 1) ≤ u j) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hs : (∑ j ∈ Finset.range (N - 1), ‖Φ (u (j + 1)) - Φ (u j)‖) ≤
      D * (u 0 - u (N - 1)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N - 1), D * (u j - u (j + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hh := hlip (u (j + 1)) (hrange (j + 1) (by omega)) (u j) (hrange j (by omega))
        rw [abs_of_nonpos (sub_nonpos.mpr (hanti j hj'))] at hh
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub']
  have hw : u 0 - u (N - 1) ≤ hi - lo := by
    have h1 := (hrange (N - 1) le_rfl).1
    have h0 := (hrange 0 (Nat.zero_le _)).2
    linarith
  exact add_le_add (hbound _ (hrange _ le_rfl))
    (hs.trans (mul_le_mul_of_nonneg_left hw hD))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialRootCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The root cells used to split the long-variable weights

A cell records the side of each real root, retaining the roots themselves as
separate cells. Polynomial inequalities are constant on a cell; polynomial
arguments are monotone when the derivative roots are included among the cuts.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem rootCellCode_no_root_between (S : Finset ℝ) {x y : ℝ}
    (hxy : x < y) (hcode : rootCellCode S x = rootCellCode S y) :
    ∀ r ∈ S, r ∉ Set.Icc x y := by
  intro r hr hrange
  have he := congrFun hcode ⟨r, hr⟩
  change compare x r = compare y r at he
  rcases lt_or_eq_of_le hrange.1 with hxr | hxr
  · have hyr : y < r := compare_lt_iff_lt.mp (he.symm.trans (compare_lt_iff_lt.mpr hxr))
    linarith [hrange.2]
  · have hyr : y = r := compare_eq_iff_eq.mp (he.symm.trans (compare_eq_iff_eq.mpr hxr))
    linarith

/-- A continuous real function with no zeros on an interval has one sign. -/
theorem continuous_sign_on_interval (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Ioo a b)) (hn : ∀ x ∈ Set.Ioo a b, f x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 ≤ f x) ∨ (∀ x ∈ Set.Ioo a b, f x ≤ 0) := by
  by_cases hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ f x
  · exact Or.inl hpos
  · right
    push Not at hpos
    obtain ⟨x, hx, hfx⟩ := hpos
    intro y hy
    by_contra hfy
    have hfy' : 0 < f y := lt_of_not_ge hfy
    obtain ⟨z, hz, hfz⟩ := isPreconnected_Ioo.intermediate_value hx hy hf
      (show (0 : ℝ) ∈ Set.Icc (f x) (f y) from ⟨hfx.le, hfy'.le⟩)
    exact hn z hz hfz

theorem polynomialRootCuts_card {I : Type*} [Fintype I] (P : I → Polynomial ℝ) :
    (polynomialRootCuts P).card ≤ ∑ i, (P i).natDegree := by
  apply (Finset.card_biUnion_le).trans
  apply Finset.sum_le_sum
  intro i _
  exact (P i).roots.toFinset_card_le.trans (P i).card_roots'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FiniteRootMesh
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite interval partition at every arithmetic root -/

namespace Ostmann
open scoped Classical

/-- Partition a bounded interval at all roots in it, retaining the roots as
endpoints. The number of intervals is at most the number of cuts plus one. -/
theorem finite_root_mesh (S : Finset ℝ) (u v : ℝ) (huv : u ≤ v) :
    ∃ (s : ℕ → ℝ) (N : ℕ), Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧
      ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (s j) (s (j + 1)) := by
  let R := insert u (insert v (S.filter (fun r => r ∈ Set.Icc u v)))
  have hu : u ∈ R := by simp [R]
  have hv : v ∈ R := by simp [R]
  have hpos : 0 < R.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hmem (r : ℝ) (hr : r ∈ R) : r ∈ Set.Icc u v := by
    simp only [R, Finset.mem_insert, Finset.mem_filter] at hr
    rcases hr with rfl | rfl | ⟨_, hr⟩
    · exact ⟨le_rfl, huv⟩
    · exact ⟨huv, le_rfl⟩
    · exact hr
  let f := R.orderEmbOfFin rfl
  have hf0 : f ⟨0, hpos⟩ = u := by
    rw [Finset.orderEmbOfFin_zero rfl hpos]
    exact le_antisymm (Finset.min'_le R u hu)
      (hmem _ (Finset.min'_mem R _)).1
  have hflast : f ⟨R.card - 1, Nat.sub_lt hpos (by decide)⟩ = v := by
    rw [Finset.orderEmbOfFin_last rfl hpos]
    exact le_antisymm (hmem _ (Finset.max'_mem R _)).2 (Finset.le_max' R v hv)
  let N := R.card - 1
  let s := fun j : ℕ => f ⟨min j N, lt_of_le_of_lt (min_le_right _ _) (by omega)⟩
  have hs : Monotone s := by
    intro i j hij
    exact f.monotone (show min i N ≤ min j N from min_le_min hij le_rfl)
  have hs0 : s 0 = u := by simpa only [s, Nat.zero_min] using hf0
  have hsN : s N = v := by simpa only [s, min_self, N] using hflast
  refine ⟨s, N, hs, hs0, hsN, ?_, ?_⟩
  · have hcard : R.card ≤ S.card + 2 := by
      calc
        R.card ≤ (insert v (S.filter (fun r => r ∈ Set.Icc u v))).card + 1 := Finset.card_insert_le _ _
        _ ≤ (S.filter (fun r => r ∈ Set.Icc u v)).card + 1 + 1 := by
          gcongr
          exact Finset.card_insert_le _ _
        _ ≤ S.card + 2 := by have := Finset.card_filter_le S (fun r => r ∈ Set.Icc u v); omega
    omega
  · intro j hj r hr hin
    have hjc : j < R.card := by omega
    have hj1c : j + 1 < R.card := by omega
    have he0 : s j = f ⟨j, hjc⟩ := by simp only [s, min_eq_left (by omega : j ≤ N)]
    have he1 : s (j + 1) = f ⟨j + 1, hj1c⟩ := by
      simp only [s, min_eq_left (by omega : j + 1 ≤ N)]
    have hrange : r ∈ Set.Icc u v :=
      ⟨(hs0 ▸ hs (Nat.zero_le j)).trans hin.1.le,
        hin.2.le.trans (hsN ▸ hs (by omega : j + 1 ≤ N))⟩
    have hrR : r ∈ R := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hr, hrange⟩))
    let k := (R.orderIsoOfFin rfl).symm ⟨r, hrR⟩
    have hk : f k = r := congrArg Subtype.val ((R.orderIsoOfFin rfl).apply_symm_apply ⟨r, hrR⟩)
    have hleft : (⟨j, hjc⟩ : Fin R.card) < k := f.lt_iff_lt.mp (by rw [← he0, hk]; exact hin.1)
    have hright : k < (⟨j + 1, hj1c⟩ : Fin R.card) := f.lt_iff_lt.mp (by rw [← he1, hk]; exact hin.2)
    have hl : j < k.val := hleft
    have hr' : k.val < j + 1 := hright
    omega

/-- The side of every root is constant in the open part of one partition cell. -/
theorem rootCellCode_eq_of_root_free (S : Finset ℝ) (a b x y : ℝ)
    (hfree : ∀ r ∈ S, r ∉ Set.Ioo a b)
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    rootCellCode S x = rootCellCode S y := by
  funext r
  change compare x r.val = compare y r.val
  by_cases hr : r.val ≤ a
  · rw [compare_gt_iff_gt.mpr (hr.trans_lt hx.1), compare_gt_iff_gt.mpr (hr.trans_lt hy.1)]
  · have hb : b ≤ r.val := by
      by_contra hb
      exact hfree r.val r.property ⟨lt_of_not_ge hr, lt_of_not_ge hb⟩
    rw [compare_lt_iff_lt.mpr (hx.2.trans_le hb), compare_lt_iff_lt.mpr (hy.2.trans_le hb)]

/-- A partition in logarithmic coordinates still includes every positive
root of the original giant-variable polynomials. -/
theorem finite_log_root_mesh (S : Finset ℝ) (u v : ℝ) (huv : u ≤ v) :
    ∃ (s : ℕ → ℝ) (N : ℕ), Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧
      ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))) := by
  obtain ⟨x, N, hx, hx0, hxN, hN, hfree⟩ :=
    finite_root_mesh S (Real.exp u) (Real.exp v) (Real.exp_le_exp.mpr huv)
  have hpos (j : ℕ) : 0 < x j := by
    have hh := hx (Nat.zero_le j)
    rw [hx0] at hh
    exact (Real.exp_pos u).trans_le hh
  let s := fun j => Real.log (x j)
  refine ⟨s, N, ?_, ?_, ?_, hN, ?_⟩
  · intro i j hij
    exact Real.log_le_log (hpos i) (hx hij)
  · simp only [s, hx0, Real.log_exp]
  · simp only [s, hxN, Real.log_exp]
  · intro j hj r hr
    simpa only [s, Real.exp_log (hpos _)] using hfree j hj r hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ContinuousPrimeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the full continuous weight with the retained Page measure -/

namespace Ostmann
open MeasureTheory

/-- A continuous weight with a uniform variation budget can be used directly
in the published progression estimate. No mesh parameter survives. -/
theorem PublishedProgressionInput.continuous_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V : ℝ)
    (hV : ∀ (s : ℕ → ℝ), Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V) :
    ‖complexPrimeInterval q a u v w -
        ∫ y in Set.Ioc u v, w y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) := by
  let M := reciprocalPrimeInterval q a (Real.exp u) (Real.exp v) + 2 * (v - u)
  have hM : 0 ≤ M := add_nonneg (reciprocalPrimeInterval_nonneg q a _ _)
    (mul_nonneg (by norm_num) (sub_nonneg.mpr huv))
  have hM1 : 0 < M + 1 := by linarith
  have hE : 0 ≤ 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
      Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) := by
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.errorConstant_nonneg)
      (Real.exp_pos _).le) (Real.exp_pos _).le
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε / (M + 1)
  have hη : 0 < η := div_pos hε hM1
  obtain ⟨s, N, _hN, hs, hs0, hsN, hosc⟩ := continuous_interval_mesh u v huv w hwc η hη
  have hc : ContinuousOn w (Set.Icc (s 0) (s N)) := by simpa only [hs0, hsN] using hwc
  have hb := P.prime_partition_variation hQ hq hqQ ha s hs
    (by simpa only [hs0] using hu) N (by simpa only [hs0, hsN] using hshort)
    w hc η hη.le hosc
  rw [hs0, hsN] at hb
  apply hb.trans
  have hvar := mul_le_mul_of_nonneg_right (hV s hs N hs0 hsN) hE
  have hsmall : η * M ≤ ε := by
    have hid : η * (M + 1) = ε := by dsimp [η]; field_simp
    nlinarith
  exact add_le_add hvar hsmall

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeExceptionalPoints
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining prime atoms on the boundaries of arithmetic root cells -/

namespace Ostmann
open scoped BigOperators Classical

/-- Changing the weight at finitely many primes costs their actual atom
masses. The estimate is uniform in the residue class and keeps endpoints. -/
theorem complexPrimeInterval_exceptional_bound (q a : ℕ) (u v : ℝ)
    (w g : ℝ → ℂ) (S : Finset ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      p.Prime → Nat.ModEq q p a → ‖w (Real.log p) - g (Real.log p)‖ ≤ B)
    (heq : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      p.Prime → Nat.ModEq q p a → p ∉ S → w (Real.log p) = g (Real.log p)) :
    ‖complexPrimeInterval q a u v w - complexPrimeInterval q a u v g‖ ≤
      (S.card : ℝ) * B * Real.exp (-u) := by
  let T := Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊
  have he : complexPrimeInterval q a u v w - complexPrimeInterval q a u v g =
      ∑ p ∈ T, if p.Prime ∧ Nat.ModEq q p a then
        (w (Real.log p) - g (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) else 0 := by
    simp only [complexPrimeInterval, ← Finset.sum_sub_distrib, T]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp [sub_mul]
  have hC : 0 ≤ B * Real.exp (-u) := mul_nonneg hB (Real.exp_pos _).le
  have hpoint (p : ℕ) (hp : p ∈ T) :
      ‖(if p.Prime ∧ Nat.ModEq q p a then
        (w (Real.log p) - g (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) else 0)‖ ≤
        if p ∈ S then B * Real.exp (-u) else 0 := by
    by_cases hs : p ∈ S
    · rw [ite_eq_left hs]
      by_cases hc : p.Prime ∧ Nat.ModEq q p a
      · rw [ite_eq_left hc, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg p)]
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hc.1.pos
        have hlog := log_mem_of_mem_exp_interval hp
        have hexp : Real.exp u ≤ (p : ℝ) := by
          calc
            Real.exp u ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr hlog.1.le
            _ = _ := Real.exp_log hp0
        have hinv : (p : ℝ)⁻¹ ≤ Real.exp (-u) := by
          rw [Real.exp_neg]
          exact inv_anti₀ (Real.exp_pos _) hexp
        exact mul_le_mul (hbound p hp hc.1 hc.2) hinv (inv_nonneg.mpr hp0.le) hB
      · simpa only [ite_eq_right hc, norm_zero] using hC
    · rw [ite_eq_right hs]
      by_cases hc : p.Prime ∧ Nat.ModEq q p a
      · simp only [ite_eq_left hc, heq p hp hc.1 hc.2 hs, sub_self, zero_mul, norm_zero, le_refl]
      · simp only [ite_eq_right hc, norm_zero, le_refl]
  rw [he]
  calc
    _ ≤ ∑ p ∈ T, ‖(if p.Prime ∧ Nat.ModEq q p a then
      (w (Real.log p) - g (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ T, if p ∈ S then B * Real.exp (-u) else 0 :=
      Finset.sum_le_sum hpoint
    _ = ((T.filter (· ∈ S)).card : ℝ) * (B * Real.exp (-u)) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (S.card : ℝ) * (B * Real.exp (-u)) := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_card (show T.filter (· ∈ S) ⊆ S from
        fun _ h => (Finset.mem_filter.mp h).2)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_OpenCellPrimeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime comparison on open root cells, with boundary atoms retained -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem complexPrimeInterval_open_cell_bound (q a : ℕ) (u v : ℝ)
    (W w : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexPrimeInterval q a u v W - complexPrimeInterval q a u v w‖ ≤
      B * Real.exp (-u) := by
  have h := complexPrimeInterval_exceptional_bound q a u v W w {⌊Real.exp v⌋₊} B hB
    (fun p hp _ _ => hbound _ (log_mem_of_mem_exp_interval hp)) (by
      intro p hp hprime _ hnot
      have hlog := log_mem_of_mem_exp_interval hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hne : Real.log p ≠ v := by
        intro he
        apply hnot
        simp only [Finset.mem_singleton]
        rw [← he, Real.exp_log hp0, Nat.floor_natCast]
      exact heq _ ⟨hlog.1, lt_of_le_of_ne hlog.2 hne⟩)
  simpa only [Finset.card_singleton, Nat.cast_one, one_mul] using h

/-- A cell's interior uses its continuous smooth factor; the right endpoint
is accounted for by its prime atom, even when it is an arithmetic root. -/
theorem PublishedProgressionInput.open_cell_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    (W w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V B : ℝ)
    (hV : ∀ s : ℕ → ℝ, Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V)
    (hB : 0 ≤ B) (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexPrimeInterval q a u v W -
      ∫ y in Set.Ioc u v, w y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) + B * Real.exp (-u) := by
  have h1 := complexPrimeInterval_open_cell_bound q a u v W w B hB hbound heq
  have h2 := P.continuous_prime_comparison hQ hq hqQ ha u v hu huv hshort w hwc V hV
  exact (norm_sub_le_norm_sub_add_norm_sub _ (complexPrimeInterval q a u v w) _).trans
    (by linarith)

/-- Sum the actual prime weights over the constructed root partition. The
ideal term is the sum of its continuous cell integrals with the Page factor. -/
theorem PublishedProgressionInput.piecewise_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) (hs0 : 1 ≤ s 0) (hshort : s N ≤ s 0 + 1)
    (W : ℝ → ℂ) (w : ℕ → ℝ → ℂ) (V B : ℕ → ℝ)
    (hwc : ∀ j < N, ContinuousOn (w j) (Set.Icc (s j) (s (j + 1))))
    (hV : ∀ j < N, ∀ r : ℕ → ℝ, Monotone r → ∀ M,
      r 0 = s j → r M = s (j + 1) → discreteVariation (fun k => w j (r k)) M ≤ V j)
    (hB : ∀ j < N, 0 ≤ B j)
    (hbound : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖W y - w j y‖ ≤ B j)
    (heq : ∀ j < N, ∀ y ∈ Set.Ioo (s j) (s (j + 1)), W y = w j y) :
    ‖complexPrimeInterval q a (s 0) (s N) W -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        w j y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N, (V j *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
          Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) + B j * Real.exp (-(s j))) := by
  rw [← complexPrimeInterval_partition q a s hs W N, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  apply P.open_cell_prime_comparison hQ hq hqQ ha _ _
    (hs0.trans (hs (Nat.zero_le _))) (hs (Nat.le_succ _))
  · have h1 := hs (by omega : j + 1 ≤ N)
    have h0 := hs (Nat.zero_le j)
    linarith
  · exact hwc j hjN
  · exact hV j hjN
  · exact hB j hjN
  · exact hbound j hjN
  · exact heq j hjN

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ProductWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of the original smooth factors retain finite variation -/

namespace Ostmann

open scoped BigOperators

theorem discreteVariation_mul (f g : ℕ → ℂ) (B D : ℝ) (N : ℕ)
    (hD : 0 ≤ D) (hf : ∀ j, ‖f j‖ ≤ B) (hg : ∀ j, ‖g j‖ ≤ D) :
    discreteVariation (fun j => f j * g j) N ≤
      B * discreteVariation g N + D * discreteVariation f N := by
  have hend : ‖f (N - 1) * g (N - 1)‖ ≤ B * ‖g (N - 1)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
  have hstep (j : ℕ) : ‖f (j + 1) * g (j + 1) - f j * g j‖ ≤
      B * ‖g (j + 1) - g j‖ + D * ‖f (j + 1) - f j‖ := by
    rw [show f (j + 1) * g (j + 1) - f j * g j =
      f (j + 1) * (g (j + 1) - g j) + (f (j + 1) - f j) * g j by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
    · simpa only [mul_comm D] using mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
  have hs := Finset.sum_le_sum (s := Finset.range (N - 1)) (fun j _ => hstep j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  unfold discreteVariation
  nlinarith [mul_nonneg hD (norm_nonneg (f (N - 1)))]

theorem discreteVariation_prod (n : ℕ) (f : Fin n → ℕ → ℂ) (B V : Fin n → ℝ) (N : ℕ)
    (hB : ∀ i, 0 ≤ B i) (hV : ∀ i, 0 ≤ V i)
    (hf : ∀ i j, ‖f i j‖ ≤ B i) (hv : ∀ i, discreteVariation (f i) N ≤ V i) :
    discreteVariation (fun j => ∏ i, f i j) N ≤ ∏ i, (B i + V i) := by
  induction n with
  | zero => simp [discreteVariation]
  | succ n ih =>
    let g : ℕ → ℂ := fun j => ∏ i : Fin n, f i.succ j
    let C : ℝ := ∏ i : Fin n, B i.succ
    let E : ℝ := ∏ i : Fin n, (B i.succ + V i.succ)
    have hC : 0 ≤ C := Finset.prod_nonneg fun i _ => hB i.succ
    have hg (j : ℕ) : ‖g j‖ ≤ C := by
      change ‖∏ i : Fin n, f i.succ j‖ ≤ C
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hf i.succ j)
    have hCE : C ≤ E := Finset.prod_le_prod (fun i _ => hB i.succ)
      (fun i _ => le_add_of_nonneg_right (hV i.succ))
    have hvg : discreteVariation g N ≤ E := ih (fun i => f i.succ) (fun i => B i.succ)
      (fun i => V i.succ) (fun i => hB i.succ) (fun i => hV i.succ)
      (fun i => hf i.succ) (fun i => hv i.succ)
    have hp : (fun j => ∏ i, f i j) = fun j => f 0 j * g j := by
      funext j
      exact Fin.prod_univ_succ _
    rw [hp, Fin.prod_univ_succ]
    apply (discreteVariation_mul (f 0) g (B 0) C N hC (hf 0) hg).trans
    calc
      _ ≤ B 0 * E + C * V 0 := add_le_add
        (mul_le_mul_of_nonneg_left hvg (hB 0)) (mul_le_mul_of_nonneg_left (hv 0) hC)
      _ ≤ B 0 * E + E * V 0 := add_le_add le_rfl (mul_le_mul_of_nonneg_right hCE (hV 0))
      _ = _ := by change B 0 * E + E * V 0 = (B 0 + V 0) * E; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialCellVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual interval pieces and smooth polynomial weights -/

namespace Ostmann

open scoped BigOperators Classical

/-- On a root cell, polynomial inequality supports really are constant. -/
theorem polynomial_nonneg_iff_of_root_cell (P : Polynomial ℝ) (S : Finset ℝ)
    (hroots : ∀ r ∈ P.roots, r ∈ S) {x y : ℝ}
    (hcode : rootCellCode S x = rootCellCode S y) :
    0 ≤ P.eval x ↔ 0 ≤ P.eval y := by
  by_cases hp : P = 0
  · simp [hp]
  have hordered (a b : ℝ) (hab : a < b)
      (hc : rootCellCode S a = rootCellCode S b) : 0 ≤ P.eval a ↔ 0 ≤ P.eval b := by
    have hn (z : ℝ) (hz : z ∈ Set.Icc a b) : P.eval z ≠ 0 := by
      intro he
      have hm : z ∈ P.roots := (Polynomial.mem_roots hp).mpr he
      exact rootCellCode_no_root_between S hab hc z (hroots z hm) hz
    constructor
    · intro ha
      by_contra hb
      have hb' : P.eval b < 0 := lt_of_not_ge hb
      obtain ⟨z, hz, he⟩ := intermediate_value_Icc' hab.le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (P.eval b) (P.eval a) from ⟨hb'.le, ha⟩)
      exact hn z hz he
    · intro hb
      by_contra ha
      have ha' : P.eval a < 0 := lt_of_not_ge ha
      obtain ⟨z, hz, he⟩ := intermediate_value_Icc hab.le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (P.eval a) (P.eval b) from ⟨ha'.le, hb⟩)
      exact hn z hz he
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact hordered x y hxy hcode
  · rfl
  · exact (hordered y x hyx hcode.symm).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ReciprocalProgressionVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original reciprocal-integer weight in partial summation -/

namespace Ostmann

open scoped BigOperators

theorem discreteVariation_const_mul (c : ℂ) (f : ℕ → ℂ) (N : ℕ) :
    discreteVariation (fun j => c * f j) N = ‖c‖ * discreteVariation f N := by
  simp only [discreteVariation, ← mul_sub, norm_mul, Finset.mul_sum, mul_add]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SmoothPolynomialWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite products of the smooth factors appearing in a history

Profiles are clipped to their prescribed argument ranges. This leaves their
values unchanged on the retained range and requires no continuity of the sharp
range indicator; those indicators are separate functions of the root cell.
-/

namespace Ostmann

open scoped BigOperators

theorem smoothPolynomialBudget_nonneg {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    0 ≤ smoothPolynomialBudget F := by
  apply Finset.prod_nonneg
  intro i _
  exact add_nonneg (mul_nonneg (by norm_num) (F i).bound_nonneg)
    (mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SmoothPrimeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime comparison for the actual clipped polynomial factors -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem continuous_smoothPolynomialWeight {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    Continuous (smoothPolynomialWeight F) :=
  continuous_finsetProd _ (fun i _ => (F i).continuous_value)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RootFreeSmoothWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth variation when roots are retained at the cell endpoints -/

namespace Ostmann
open scoped BigOperators

theorem polynomial_monotoneOn_no_roots (P : Polynomial ℝ) (a b : ℝ)
    (hroots : ∀ r ∈ P.derivative.roots, r ∉ Set.Ioo a b) :
    MonotoneOn P.eval (Set.Icc a b) ∨ AntitoneOn P.eval (Set.Icc a b) := by
  by_cases hd : P.derivative = 0
  · left
    have hp := Polynomial.eq_C_of_derivative_eq_zero hd
    intro x hx y hy hxy
    have hv (t : ℝ) : P.eval t = P.coeff 0 := by
      have hh := congrArg (fun Q : Polynomial ℝ => Q.eval t) hp
      simpa only [Polynomial.eval_C] using hh
    change P.eval x ≤ P.eval y
    rw [hv x, hv y]
  · have hn : ∀ x ∈ Set.Ioo a b, P.derivative.eval x ≠ 0 := by
      intro x hx hz
      exact hroots x ((Polynomial.mem_roots hd).mpr hz) hx
    rcases continuous_sign_on_interval P.derivative.eval a b
        P.derivative.continuous.continuousOn hn with hpos | hneg
    · left
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hpos x hx
    · right
      apply antitoneOn_of_deriv_nonpos (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hneg x hx

theorem ClippedPolynomialFactor.variation_no_roots (f : ClippedPolynomialFactor)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hroots : ∀ r ∈ f.polynomial.derivative.roots, r ∉ Set.Ioo (u 0) (u (N - 1))) :
    discreteVariation (fun j => f.value (u j)) N ≤ f.bound + f.lip * (f.hi - f.lo) := by
  let v : ℕ → ℝ := fun j => clipRealInterval f.lo f.hi (f.polynomial.eval (u j))
  have hr (j : ℕ) (_hj : j ≤ N - 1) : v j ∈ Set.Icc f.lo f.hi :=
    clipRealInterval_bounds f.lo f.hi _ f.lo_le_hi
  have hu' (j : ℕ) (hj : j ≤ N - 1) : u j ∈ Set.Icc (u 0) (u (N - 1)) :=
    ⟨hu (Nat.zero_le _), hu hj⟩
  change discreteVariation (fun j => f.profile (v j)) N ≤ _
  rcases polynomial_monotoneOn_no_roots f.polynomial (u 0) (u (N - 1)) hroots with hm | hm
  · apply discreteVariation_comp_monotoneOn f.profile v f.lo f.hi f.bound f.lip N
      f.lip_nonneg f.norm_le f.lipschitz hr
    intro j hj
    exact clipRealInterval_monotone f.lo f.hi
      (hm (hu' j hj.le) (hu' (j + 1) (by omega)) (hu (by omega)))
  · apply discreteVariation_comp_antitoneOn f.profile v f.lo f.hi f.bound f.lip N
      f.lip_nonneg f.norm_le f.lipschitz hr
    intro j hj
    exact clipRealInterval_monotone f.lo f.hi
      (hm (hu' j hj.le) (hu' (j + 1) (by omega)) (hu (by omega)))

theorem smoothPolynomialWeight_variation_no_roots {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots →
      r ∉ Set.Ioo (u 0) (u (N - 1))) :
    discreteVariation (fun j => smoothPolynomialWeight F (u j)) N ≤ smoothPolynomialBudget F := by
  have hV (i : Fin n) : 0 ≤ (F i).bound + (F i).lip * ((F i).hi - (F i).lo) :=
    add_nonneg (F i).bound_nonneg
      (mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi))
  have ht := discreteVariation_prod n (fun i j => (F i).value (u j))
    (fun i => (F i).bound) (fun i => (F i).bound + (F i).lip * ((F i).hi - (F i).lo)) N
    (fun i => (F i).bound_nonneg) hV (fun i j => (F i).norm_value (u j))
    (fun i => (F i).variation_no_roots u hu N (hroots i))
  change discreteVariation (fun j => ∏ i, (F i).value (u j)) N ≤ _
  apply ht.trans_eq
  apply Finset.prod_congr rfl
  intro i _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CommonRootMesh
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One explicit root mesh for all residue classes -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem rootMeshWeight_continuous {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (s : ℕ → ℝ) (j : ℕ) : Continuous (rootMeshWeight F w s j) :=
  continuous_const.mul ((continuous_smoothPolynomialWeight F).comp Real.continuous_exp)

theorem rootMeshWeight_variation {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (S : Finset ℝ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (s : ℕ → ℝ) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (j : ℕ) (hj : j < N) (r : ℕ → ℝ) (hr : Monotone r) (M : ℕ)
    (hr0 : r 0 = s j) (hrM : r M = s (j + 1)) :
    discreteVariation (fun l => rootMeshWeight F w s j (r l)) M ≤
      ‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F := by
  unfold rootMeshWeight
  rw [discreteVariation_const_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply smoothPolynomialWeight_variation_no_roots F (fun l => Real.exp (r l))
    (Real.exp_monotone.comp hr) M
  intro i x hx hxin
  apply hfree j hj x (hroots i x hx)
  refine ⟨?_, ?_⟩
  · simpa only [hr0] using hxin.1
  · have hlast : Real.exp (r (M - 1)) ≤ Real.exp (s (j + 1)) := by
      rw [← hrM]
      exact Real.exp_le_exp.mpr (hr (Nat.sub_le M 1))
    exact hxin.2.trans_le hlast

theorem rootMeshWeight_bound {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (s : ℕ → ℝ) (j : ℕ) (y : ℝ) :
    ‖w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) - rootMeshWeight F w s j y‖ ≤
      2 * C * smoothPolynomialBudget F := by
  calc
    _ ≤ ‖w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)‖ +
        ‖rootMeshWeight F w s j y‖ := norm_sub_le _ _
    _ ≤ C * smoothPolynomialBudget F + C * smoothPolynomialBudget F := by
      simp only [rootMeshWeight, norm_mul]
      exact add_le_add
        (mul_le_mul (hw _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
        (mul_le_mul (hw _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
    _ = _ := by ring

theorem rootMeshWeight_eq {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (S : Finset ℝ)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y)
    (s : ℕ → ℝ) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (j : ℕ) (hj : j < N) (y : ℝ) (hy : y ∈ Set.Ioo (s j) (s (j + 1))) :
    w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) = rootMeshWeight F w s j y := by
  unfold rootMeshWeight
  congr 1
  apply hconst
  apply rootCellCode_eq_of_root_free S (Real.exp (s j)) (Real.exp (s (j + 1)))
    (Real.exp y) (Real.exp ((s j + s (j + 1)) / 2)) (hfree j hj)
  · exact ⟨Real.exp_lt_exp.mpr hy.1, Real.exp_lt_exp.mpr hy.2⟩
  · constructor <;> apply Real.exp_lt_exp.mpr <;> linarith [hy.1, hy.2]

/-- The mesh is supplied before the residue class and coefficient. -/
theorem PublishedProgressionInput.common_root_mesh_prime_comparison (P : PublishedProgressionInput)
    (S : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (hu : 1 ≤ s 0) (hshort : s N ≤ s 0 + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexPrimeInterval q a (s 0) (s N)
        (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        rootMeshWeight F w s j y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
            Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
          2 * C * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  apply P.piecewise_prime_comparison hQ hq hqQ ha s hs N hu hshort
    _ (rootMeshWeight F w s) _ _
  · exact fun j _ => (rootMeshWeight_continuous F w s j).continuousOn
  · exact fun j hj r hr M hr0 hrM => rootMeshWeight_variation F w S hroots s N hfree j hj r hr M hr0 hrM
  · exact fun _ _ => mul_nonneg (mul_nonneg (by positivity) hC) (smoothPolynomialBudget_nonneg F)
  · exact fun j _ y _ => rootMeshWeight_bound F w C hC hw s j y
  · exact fun j hj y hy => rootMeshWeight_eq F w S hconst s N hfree j hj y hy

theorem common_root_mesh_integer_comparison
    (S : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (q a : ℕ) (hq : 0 < q) (G : ℝ)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexIntegerInterval q a (s 0) (s N) G
        (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        rootMeshWeight F w s j y * (integerLogDensity q G y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (2 * Real.exp (-G)) + 2 * C * smoothPolynomialBudget F * Real.exp (-G)) := by
  apply piecewise_integer_comparison q a hq G s hs N
    _ (rootMeshWeight F w s) _ _
  · exact fun j _ => (rootMeshWeight_continuous F w s j).continuousOn
  · exact fun j hj r hr M hr0 hrM => rootMeshWeight_variation F w S hroots s N hfree j hj r hr M hr0 hrM
  · exact fun _ _ => mul_nonneg (mul_nonneg (by positivity) hC) (smoothPolynomialBudget_nonneg F)
  · exact fun j _ y _ => rootMeshWeight_bound F w C hC hw s j y
  · exact fun j hj y hy => rootMeshWeight_eq F w S hconst s N hfree j hj y hy

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialWeightPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual off-diagonal product of two polynomial weights -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem pairedPolynomialFactors_weight {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) (x : ℝ) :
    smoothPolynomialWeight (pairedPolynomialFactors F G) x =
      smoothPolynomialWeight F x * conj (smoothPolynomialWeight G x) := by
  simp only [smoothPolynomialWeight, pairedPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate_value, map_prod]

theorem pairedPolynomialFactors_budget {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) :
    smoothPolynomialBudget (pairedPolynomialFactors F G) =
      smoothPolynomialBudget F * smoothPolynomialBudget G := by
  simp only [smoothPolynomialBudget, pairedPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryFormula
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual product-and-pivot formulas of a fixed arithmetic history -/

namespace Ostmann

namespace HistoryFormula

variable {σ : Type*}

theorem degree_le_cost (F : HistoryFormula σ) : F.cleared.numerator.totalDegree ≤ F.cost := by
  induction F with
  | prime i => simp [cleared, cost, ClearedHistoryValue.ofVariable]
  | external z =>
    simp only [cleared, cost, ClearedHistoryValue.constant, MvPolynomial.totalDegree_C]
    omega
  | product f g ihf ihg =>
    apply (ClearedHistoryValue.degree_prod _ _).trans
    simpa only [Fintype.sum_bool, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, cost] using
      Nat.add_le_add ihf ihg
  | solve f g v w s hs ihf ihg =>
    apply (ClearedHistoryValue.degree_pivot f.cleared g.cleared v w s hs).trans
    exact max_le (by dsimp only [cost]; omega) (by dsimp only [cost]; omega)

end HistoryFormula

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedHistoryGuards
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact range and residue guards for the reconstructed original pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem formulaPolynomial_degree {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℝ) (coord : σ) : (formulaPolynomial F a coord).natDegree ≤ F.cost :=
  (normalizedHistoryPolynomial_natDegree _ _ _ _).trans F.degree_le_cost

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantArchimedean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual terminal moduli as quadratic functions of a top giant

Small prime values are fixed here. Every reconstructed giant is linear in the
initial pair, and each terminal modulus is a product of two such linear forms.
The identification uses the integer support equations of the original sampler.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.pivotPolynomial_eval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : Polynomial ℝ) (z : ℝ) :
    (s.pivotPolynomial value XL XR).eval z = s.realPivot value (XL.eval z) (XR.eval z) := by
  simp only [pivotPolynomial, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    realPivot, div_eq_mul_inv]
  ring

theorem MovingSlotReversal.pivotPolynomial_degree {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : Polynomial ℝ) (d : ℕ)
    (hL : XL.natDegree ≤ d) (hR : XR.natDegree ≤ d) :
    (s.pivotPolynomial value XL XR).natDegree ≤ d := by
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, zero_add] using hR)
  · exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, zero_add] using hL)

theorem MovingSlotData.leafPolynomials_degree {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : Polynomial ℝ) (d : ℕ)
    (hL : XL.natDegree ≤ d) (hR : XR.natDegree ≤ d) (i : TreeLeafIndex n) :
    (T.leafPolynomials value XL XR i).natDegree ≤ 2 * d := by
  induction T generalizing XL XR with
  | leaf s regular =>
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, add_zero]
    exact Polynomial.natDegree_mul_le.trans (by omega)
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).pivotPolynomial_degree
      value XL XR d hL hR
    cases i with
    | inl i => exact ihL _ _ hp hL i
    | inr i => exact ihR _ _ hp hR i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete polynomial factors in the moving Fourier history -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem movingLeafNormalizedPolynomial_eval {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X z : ℝ) (i : TreeLeafIndex n) :
    (movingLeafNormalizedPolynomial value T L R X i).eval z =
      (T.leafPolynomials value L R i).eval z / X := by
  simp only [movingLeafNormalizedPolynomial, Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv]
  ring

theorem movingFourierPolynomialFactors_degree {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1) (j : Fin (2 ^ n)) :
    (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi j).polynomial.natDegree ≤ 2 := by
  have hp := T.leafPolynomials_degree value L R 1 hL hR ((movingLeafIndexEquiv n).symm j)
  have hn : (movingLeafNormalizedPolynomial value T L R X
      ((movingLeafIndexEquiv n).symm j)).natDegree ≤ 2 := by
    apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C, zero_add, mul_one] using hp
  dsimp only [movingFourierPolynomialFactors]
  split_ifs <;> exact hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed variation bounds for the actual moving Fourier factors -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingFourierPolynomialFactors_budget {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) :
    smoothPolynomialBudget (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) ≤
      movingFourierVariationBudget ψ V lo hi n := by
  unfold smoothPolynomialBudget movingFourierVariationBudget
  calc
    _ ≤ ∏ _j : Fin (2 ^ n),
        (2 * SchwartzMap.seminorm ℝ 0 0 ψ +
          (SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * V) * (hi - lo)) := by
      apply Finset.prod_le_prod
      · intro j _
        let f := movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi j
        exact add_nonneg (mul_nonneg (by norm_num) f.bound_nonneg)
          (mul_nonneg f.lip_nonneg (sub_nonneg.mpr f.lo_le_hi))
      · intro j _
        have hv := T.leafFrequencies_bound V hV ((movingLeafIndexEquiv n).symm j)
        have hd := mul_le_mul_of_nonneg_left hv (schwartz_profile_lip_nonneg ψ)
        have he := mul_le_mul_of_nonneg_right (add_le_add (le_rfl : SchwartzMap.seminorm ℝ 0 0 ψ ≤ SchwartzMap.seminorm ℝ 0 0 ψ) hd)
          (sub_nonneg.mpr hhi)
        dsimp only [movingFourierPolynomialFactors]
        split_ifs <;> exact add_le_add le_rfl he
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFormulaNodes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All rational node formulas of the concrete moving sampler -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.formulaNodes_length {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (L R : HistoryFormula Bool) :
    (T.formulaNodes value hvalue childBound pivotBound hf L R).length = 2 ^ n - 1 := by
  induction T generalizing L R with
  | leaf s regular => rfl
  | @node n s CL CR u left right ihL ihR =>
    simp only [formulaNodes, List.length_cons, List.length_append, ihL, ihR, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact root-cell multipliers for the original moving arithmetic support -/

namespace Ostmann
open scoped Classical

theorem rootCellCode_eq_of_subset (S T : Finset ℝ) (hST : S ⊆ T) (x y : ℝ)
    (h : rootCellCode T x = rootCellCode T y) : rootCellCode S x = rootCellCode S y := by
  funext r
  exact congrFun h ⟨r.val, hST r.property⟩

theorem complexPrimeInterval_congr (q a : ℕ) (u v : ℝ) (w g : ℝ → ℂ)
    (h : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      p.Prime → Nat.ModEq q p a → w (Real.log p) = g (Real.log p)) :
    complexPrimeInterval q a u v w = complexPrimeInterval q a u v g := by
  unfold complexPrimeInterval
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hc : p.Prime ∧ Nat.ModEq q p a
  · simp only [ite_eq_left hc, h p hp hc.1 hc.2]
  · simp only [ite_eq_right hc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCutoffPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All actual logarithmic node cutoffs as polynomial factors -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotData.nodeCutoffPolynomials_length {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) :
    (T.nodeCutoffPolynomials value L R).length = 2 ^ n - 1 := by
  induction T generalizing L R with
  | leaf => rfl
  | @node n s CL CR u left right ihL ihR =>
    simp only [nodeCutoffPolynomials, List.length_cons, List.length_append, ihL, ihR, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem MovingSlotData.nodeCutoffPolynomials_degree {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (d : ℕ)
    (hL : L.natDegree ≤ d) (hR : R.natDegree ≤ d) :
    ∀ f ∈ T.nodeCutoffPolynomials value L R, f.2.natDegree ≤ d := by
  induction T generalizing L R with
  | leaf => simp [nodeCutoffPolynomials]
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).pivotPolynomial_degree value L R d hL hR
    intro f hf
    rcases List.mem_cons.mp hf with h | h
    · subst f; exact hp
    · exact (List.mem_append.mp h).elim (ihL _ _ hp hL f) (ihR _ _ hp hR f)

theorem MovingSlotData.nodeCutoffPolynomials_value {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (z : ℝ) :
    ((T.nodeCutoffPolynomials value L R).map
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval z) : ℂ))).prod =
      movingRealNodeCutoff value φ G T (L.eval z) (R.eval z) := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [nodeCutoffPolynomials, List.map_cons, List.map_append, List.prod_cons,
      List.prod_append, ihL, ihR, MovingSlotReversal.pivotPolynomial_eval, movingRealNodeCutoff]
    ring

theorem movingNodeCutoffFactors_value {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    smoothPolynomialWeight (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip) z =
      movingRealNodeCutoff value φ G T (L.eval z) (R.eval z) := by
  unfold smoothPolynomialWeight
  simp only [movingNodeCutoffFactors, logCutoffPolynomialFactor_value _ _ _ _ _ _ _ hφ hlip hout]
  rw [← T.nodeCutoffPolynomials_value value φ G L R z]
  exact (Fin.prod_ofFn _).symm.trans (congrArg List.prod
    (List.ofFn_getElem_eq_map (T.nodeCutoffPolynomials value L R)
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval z) : ℂ))))

theorem movingNodeCutoffFactors_budget {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip) =
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  unfold smoothPolynomialBudget
  simp only [movingNodeCutoffFactors, logCutoffPolynomialFactor_budget, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, T.nodeCutoffPolynomials_length]

/-- With either top giant fixed, all node cutoff polynomials are affine.
Thus their derivatives have no roots and need no additional partition cuts. -/
theorem movingNodeCutoffFactors_no_derivative_roots {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (i : Fin (T.nodeCutoffPolynomials value L R).length) :
    ((movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip i).polynomial.derivative).roots = 0 := by
  have hp := T.nodeCutoffPolynomials_degree value L R 1 hL hR _ (List.getElem_mem i.isLt)
  change (T.nodeCutoffPolynomials value L R)[i].2.natDegree ≤ 1 at hp
  have hd := Polynomial.natDegree_derivative_le (T.nodeCutoffPolynomials value L R)[i].2
  have hc := Polynomial.card_roots' ((T.nodeCutoffPolynomials value L R)[i].2.derivative)
  apply Multiset.card_eq_zero.mp
  change ((T.nodeCutoffPolynomials value L R)[i].2.derivative).roots.card = 0
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingIntegerCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal moving arithmetic and spectator weights for integer giants -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem complexIntegerInterval_congr (q a : ℕ) (u v G : ℝ) (w g : ℝ → ℂ)
    (h : ∀ n ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      Nat.ModEq q n a → w (Real.log n) = g (Real.log n)) :
    complexIntegerInterval q a u v G w = complexIntegerInterval q a u v G g := by
  unfold complexIntegerInterval
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : Nat.ModEq q n a
  · rw [h n hn hc]
  · simp only [integerResidueAtom, ite_eq_right hc, Complex.ofReal_zero, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original arithmetic gate into residues and real inequalities -/

namespace Ostmann
open scoped Classical

theorem WordTransferGuard.archimedeanAt_polynomials {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℝ) (coord : σ) (z : ℝ) :
    g.archimedeanAt (Function.update a coord z) ↔
      ∀ j, 0 ≤ (g.realPolynomials a coord j).eval z := by
  simp only [archimedeanAt, realPolynomials, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.forall_fin_zero,
    Polynomial.eval_sub, Polynomial.eval_C, formulaPolynomial, normalizedHistoryPolynomial_eval,
    HistoryFormula.realEval, sub_nonneg, and_true]

theorem WordTransferGuard.realPolynomials_degree {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℝ) (coord : σ) (j : Fin 3) :
    (g.realPolynomials a coord j).natDegree ≤ max g.pivot.cost g.rightProduct.cost := by
  fin_cases j
  · apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_zero]
    exact (formulaPolynomial_degree _ _ _).trans (Nat.le_max_left _ _)
  · apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, zero_max]
    exact (formulaPolynomial_degree _ _ _).trans (Nat.le_max_left _ _)
  · apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_zero]
    exact (formulaPolynomial_degree _ _ _).trans (Nat.le_max_right _ _)

theorem movingArchimedeanRootCuts_mem (nodes : List MovingFormulaNode)
    (a : Bool → ℝ) (coord : Bool) (f : MovingFormulaNode) (hf : f ∈ nodes)
    (j : Fin 3) (r : ℝ) (hr : r ∈ (f.guard.realPolynomials a coord j).roots) :
    r ∈ movingArchimedeanRootCuts nodes a coord := by
  exact Finset.mem_biUnion.mpr ⟨f, List.mem_toFinset.mpr hf,
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩⟩

theorem movingArchimedeanGate_rootCell (nodes : List MovingFormulaNode)
    (a : Bool → ℝ) (coord : Bool) (S : Finset ℝ)
    (hS : movingArchimedeanRootCuts nodes a coord ⊆ S) (x y : ℝ)
    (hcode : rootCellCode S x = rootCellCode S y) :
    movingArchimedeanGate nodes (movingRealUpdate a coord x) ↔
      movingArchimedeanGate nodes (movingRealUpdate a coord y) := by
  apply forall_congr'
  intro f
  apply imp_congr_right
  intro hf
  dsimp only [movingRealUpdate]
  rw [f.guard.archimedeanAt_polynomials a coord x, f.guard.archimedeanAt_polynomials a coord y]
  apply forall_congr'
  intro j
  exact polynomial_nonneg_iff_of_root_cell _ S
    (fun r hr => hS (movingArchimedeanRootCuts_mem nodes a coord f hf j r hr)) hcode

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWindowCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sharp terminal windows have explicit polynomial root cells -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingWindowPolynomials_mem_iff {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi z : ℝ) :
    (∀ i, (movingLeafNormalizedPolynomial value T L R X i).eval z ∈ Set.Icc lo hi) ↔
      ∀ i, 0 ≤ (movingWindowPolynomials value T L R X lo hi i).eval z := by
  constructor
  · intro h i
    cases hb : i.2
    · simpa only [movingWindowPolynomials, hb, Bool.false_eq_true, ite_false, if_false,
        Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg] using (h i.1).1
    · simpa only [movingWindowPolynomials, hb, ite_true, if_true,
        Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg] using (h i.1).2
  · intro h i
    constructor
    · simpa only [movingWindowPolynomials, Bool.false_eq_true, ite_false, if_false,
        Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg] using h (i, false)
    · simpa only [movingWindowPolynomials, ite_true, if_true,
        Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg] using h (i, true)

theorem movingWindowRootCuts_card {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi : ℝ)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1) :
    (movingWindowRootCuts value T L R X lo hi).card ≤ 4 * 2 ^ n := by
  have hp (i : TreeLeafIndex n) : (movingLeafNormalizedPolynomial value T L R X i).natDegree ≤ 2 := by
    apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C, zero_add, mul_one] using T.leafPolynomials_degree value L R 1 hL hR i
  have hdeg (i : TreeLeafIndex n × Bool) :
      (movingWindowPolynomials value T L R X lo hi i).natDegree ≤ 2 := by
    unfold movingWindowPolynomials
    split_ifs
    · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) (hp i.1))
    · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hp i.1) (by simp))
  apply (polynomialRootCuts_card _).trans
  calc
    _ ≤ ∑ _i : TreeLeafIndex n × Bool, 2 := Finset.sum_le_sum (fun i _ => hdeg i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_bool, card_treeLeafIndex, smul_eq_mul]; omega

theorem movingPolynomialWindows_of_rootCell {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi x y : ℝ)
    (S : Finset ℝ) (hS : movingWindowRootCuts value T L R X lo hi ⊆ S)
    (hcode : rootCellCode S x = rootCellCode S y) :
    (∀ i, (movingLeafNormalizedPolynomial value T L R X i).eval x ∈ Set.Icc lo hi) ↔
      (∀ i, (movingLeafNormalizedPolynomial value T L R X i).eval y ∈ Set.Icc lo hi) := by
  rw [movingWindowPolynomials_mem_iff, movingWindowPolynomials_mem_iff]
  apply forall_congr'
  intro i
  apply polynomial_nonneg_iff_of_root_cell _ S _ hcode
  intro r hr
  exact hS (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSmoothPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One polynomial family for all node cutoffs and Fourier leaves -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingSmoothPolynomialFactors_value {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip) z =
      smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z *
        movingRealNodeCutoff value φ G T (L.eval z) (R.eval z) := by
  simp only [smoothPolynomialWeight, movingSmoothPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right]
  exact congrArg (_ * ·) (movingNodeCutoffFactors_value value T L R φ G B D hB hD hφ hlip hout z)

theorem movingSmoothPolynomialFactors_budget {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip) ≤
      movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  have he : smoothPolynomialBudget (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
        φ G B D hB hD hφ hlip) =
      smoothPolynomialBudget (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) *
        smoothPolynomialBudget (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip) := by
    simp only [smoothPolynomialBudget, movingSmoothPolynomialFactors, Fin.prod_univ_add,
      Fin.append_left, Fin.append_right]
  rw [he, movingNodeCutoffFactors_budget]
  apply mul_le_mul_of_nonneg_right
    (movingFourierPolynomialFactors_budget value T L R ψ X lo hi V hlo hhi hV)
  have he2 : 0 ≤ Real.exp (2 : ℝ) - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealWindows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The terminal-window factor on two real giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotData.leafPolynomials_real {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (z : ℝ) (i : TreeLeafIndex n) :
    (T.leafPolynomials value L R i).eval z = T.realLeafModuli value (L.eval z) (R.eval z) i := by
  induction T generalizing L R with
  | leaf => simp only [leafPolynomials, realLeafModuli, Polynomial.eval_mul, Polynomial.eval_C]
  | node s CL CR U left right ihL ihR =>
    cases i with
    | inl i =>
      simpa only [leafPolynomials, realLeafModuli, MovingSlotReversal.pivotPolynomial_eval] using
        ihL ((MovingSlotData.step s CL CR U left right false).pivotPolynomial value L R) L i
    | inr i =>
      simpa only [leafPolynomials, realLeafModuli, MovingSlotReversal.pivotPolynomial_eval] using
        ihR ((MovingSlotData.step s CL CR U left right false).pivotPolynomial value L R) R i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRootBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite root budgets for the exact moving arithmetic support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingNodeGuard_cost (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) :
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).pivot.cost = L.cost + R.cost + 6 ∧
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).rightProduct.cost = R.cost + 2 := by
  simp [movingNodeGuard, wordTransferGuard, wordTransferStep, movingNodeWord,
    HistoryPivotStep.formula, HistoryFormula.bind, HistoryFormula.listProduct, HistoryFormula.cost]
  omega

theorem MovingSlotData.formulaNodes_cost {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (L R : HistoryFormula Bool)
    (D : ℕ) (hL : L.cost ≤ D) (hR : R.cost ≤ D) :
    ∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R,
      max f.guard.pivot.cost f.guard.rightProduct.cost ≤ 2 ^ n * (D + 6) := by
  induction T generalizing L R D with
  | leaf => simp [formulaNodes]
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    let G := step.giantFormula value hf.1 (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R
    have hG : G.cost ≤ 2 * D + 4 := by
      dsimp [G, MovingSlotReversal.giantFormula, HistoryFormula.cost]
      omega
    have hd : D ≤ 2 * D + 4 := by omega
    have hl := ihL hf.2.1 G L (2 * D + 4) hG (hL.trans hd)
    have hr := ihR hf.2.2 G R (2 * D + 4) hG (hR.trans hd)
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have he : 2 ^ n * (2 * D + 4 + 6) ≤ 2 ^ (n + 1) * (D + 6) := by
      rw [pow_succ]; nlinarith
    intro f hmem
    rcases List.mem_cons.mp hmem with h | h
    · subst f
      have hc := movingNodeGuard_cost (MovingSlotReversal.naturalProduct value CL)
        (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hf.1
        (childBound (n + 1)) (pivotBound (n + 1)) L R
      apply max_le
      · rw [hc.1]
        rw [pow_succ]
        nlinarith
      · rw [hc.2]
        rw [pow_succ]
        nlinarith
    · rcases List.mem_append.mp h with h | h
      · exact (hl f h).trans he
      · exact (hr f h).trans he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residue-independent cells for either real giant coordinate -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRealPair_update (coord : Bool) (fixed z : ℝ) :
    movingRealPair coord fixed z = movingRealUpdate (topGiantReal fixed fixed) coord z := by
  funext b
  cases coord <;> cases b <;> simp [movingRealPair, movingRealUpdate, topGiantReal]

theorem movingCoordinate_eval (coord : Bool) (fixed z : ℝ) :
    (movingCoordinateLeft coord fixed).eval z = movingRealPair coord fixed z false ∧
    (movingCoordinateRight coord fixed).eval z = movingRealPair coord fixed z true := by
  cases coord <;> simp [movingCoordinateLeft, movingCoordinateRight, movingRealPair, topGiantReal]

theorem movingRealGateWeight_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ)
    (x : Bool → ℝ) : ‖movingRealGateWeight value T nodes X lo hi x‖ ≤ 1 := by
  unfold movingRealGateWeight movingArchimedeanFlag movingRealWindowFlag
  split_ifs <;> norm_num

theorem movingArchimedeanRootCuts_card (nodes : List MovingFormulaNode)
    (a : Bool → ℝ) (coord : Bool) :
    (movingArchimedeanRootCuts nodes a coord).card ≤
      ∑ f ∈ nodes.toFinset, ∑ j : Fin 3, (f.guard.realPolynomials a coord j).natDegree := by
  apply (Finset.card_biUnion_le).trans
  exact Finset.sum_le_sum fun f _ => polynomialRootCuts_card (f.guard.realPolynomials a coord)

theorem movingRealRootCuts_card {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (X lo hi : ℝ)
    (coord : Bool) (fixed : ℝ) :
    (movingRealRootCuts value T
      (T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true))
      X lo hi coord fixed).card ≤ (2 ^ n - 1) * (3 * (7 * 2 ^ n)) + 4 * 2 ^ n := by
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  have hcost := T.formulaNodes_cost value hvalue childBound pivotBound hf
    (.prime false) (.prime true) 1 (by rfl) (by rfl)
  have ha : (movingArchimedeanRootCuts nodes (topGiantReal fixed fixed) coord).card ≤
      (2 ^ n - 1) * (3 * (7 * 2 ^ n)) := by
    apply (movingArchimedeanRootCuts_card nodes _ coord).trans
    calc
      _ ≤ ∑ _f ∈ nodes.toFinset, 3 * (7 * 2 ^ n) := by
        apply Finset.sum_le_sum
        intro f hf
        calc
          _ ≤ ∑ _j : Fin 3, 7 * 2 ^ n := by
            apply Finset.sum_le_sum
            intro j _
            apply (f.guard.realPolynomials_degree _ _ j).trans
            simpa only [Nat.reduceAdd, mul_comm] using hcost f (List.mem_toFinset.mp hf)
          _ = _ := by simp
      _ = nodes.toFinset.card * (3 * (7 * 2 ^ n)) := by simp
      _ ≤ nodes.length * (3 * (7 * 2 ^ n)) :=
        Nat.mul_le_mul_right _ (List.toFinset_card_le nodes)
      _ = _ := by rw [MovingSlotData.formulaNodes_length]
  have hw := movingWindowRootCuts_card value T (movingCoordinateLeft coord fixed)
    (movingCoordinateRight coord fixed) X lo hi
    (by cases coord <;> simp [movingCoordinateLeft])
    (by cases coord <;> simp [movingCoordinateRight])
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add ha hw)

/-- These cells depend on the real fixed giant, never on residue representatives. -/
theorem movingRealGateWeight_rootCell {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ)
    (coord : Bool) (fixed x y : ℝ) (S : Finset ℝ)
    (hS : movingRealRootCuts value T nodes X lo hi coord fixed ⊆ S)
    (hcode : rootCellCode S x = rootCellCode S y) :
    movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed x) =
      movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed y) := by
  have ha := movingArchimedeanGate_rootCell nodes (topGiantReal fixed fixed) coord S
    (fun r hr => hS (Finset.mem_union_left _ hr)) x y hcode
  rw [← movingRealPair_update, ← movingRealPair_update] at ha
  have hw := movingPolynomialWindows_of_rootCell value T (movingCoordinateLeft coord fixed)
    (movingCoordinateRight coord fixed) X lo hi x y S
    (fun r hr => hS (Finset.mem_union_right _ hr)) hcode
  have hev (z : ℝ) (i : TreeLeafIndex n) :
      (movingLeafNormalizedPolynomial value T (movingCoordinateLeft coord fixed)
        (movingCoordinateRight coord fixed) X i).eval z =
      T.realLeafModuli value (movingRealPair coord fixed z false)
        (movingRealPair coord fixed z true) i / X := by
    rw [movingLeafNormalizedPolynomial_eval, T.leafPolynomials_real]
    rw [(movingCoordinate_eval coord fixed z).1, (movingCoordinate_eval coord fixed z).2]
  simp only [hev] at hw
  unfold movingRealGateWeight movingArchimedeanFlag movingRealWindowFlag
  simp only [ha, hw]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RootMeshIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reassembling root cells into the original real integral -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem rootMeshWeight_integral {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (S : Finset ℝ)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (ρ : ℝ → ℂ) (hρ : ContinuousOn ρ (Set.Icc (s 0) (s N))) :
    IntervalIntegrable (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) * ρ y)
      volume (s 0) (s N) ∧
    (∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
      rootMeshWeight F w s j y * ρ y) =
      ∫ y in Set.Ioc (s 0) (s N),
        w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) * ρ y := by
  let f := fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) * ρ y
  have heq (j : ℕ) (hj : j < N) (y : ℝ) (hy : y ∈ Set.Ioo (s j) (s (j + 1))) :
      rootMeshWeight F w s j y * ρ y = f y := by
    rw [← rootMeshWeight_eq F w S hconst s N hfree j hj y hy]
  have hc (j : ℕ) (hj : j < N) :
      IntervalIntegrable (fun y => rootMeshWeight F w s j y * ρ y) volume (s j) (s (j + 1)) := by
    apply ((rootMeshWeight_continuous F w s j).continuousOn.mul (hρ.mono ?_)).intervalIntegrable_of_Icc
      (hs (Nat.le_succ _))
    intro y hy
    exact ⟨(hs (Nat.zero_le _)).trans hy.1, hy.2.trans (hs (by omega))⟩
  have hf (j : ℕ) (hj : j < N) : IntervalIntegrable f volume (s j) (s (j + 1)) := by
    apply (hc j hj).congr_uIoo
    rw [Set.uIoo_of_le (hs (Nat.le_succ _))]
    exact heq j hj
  refine ⟨IntervalIntegrable.trans_iterate hf, ?_⟩
  have heqI (j : ℕ) (hj : j < N) :
      (∫ y in Set.Ioc (s j) (s (j + 1)), rootMeshWeight F w s j y * ρ y) =
        ∫ y in (s j)..(s (j + 1)), f y := by
    rw [← intervalIntegral.integral_of_le (hs (Nat.le_succ _))]
    exact intervalIntegral.integral_congr_Ioo_of_le (hs (Nat.le_succ _)) (heq j hj)
  calc
    _ = ∑ j ∈ Finset.range N, ∫ y in (s j)..(s (j + 1)), f y := by
      apply Finset.sum_congr rfl
      intro j hj
      exact heqI j (Finset.mem_range.mp hj)
    _ = ∫ y in (s 0)..(s N), f y := intervalIntegral.sum_integral_adjacent_intervals hf
    _ = _ := intervalIntegral.integral_of_le (hs (Nat.zero_le _))

/-- No root-dependent main term survives the partition. The full density
and the sharp real gate remain inside one integral. -/
theorem PublishedProgressionInput.common_root_prime_integral (P : PublishedProgressionInput)
    (S : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (hu : 1 ≤ s 0) (hshort : s N ≤ s 0 + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexPrimeInterval q a (s 0) (s N)
        (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc (s 0) (s N), w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
        (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
            Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
          2 * C * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  have h := P.common_root_mesh_prime_comparison S s hs N hfree hQ hq hqQ ha hu hshort F hroots
    w C hC hw hconst
  have hρ : ContinuousOn (fun y => (selectedPrimeLogDensity P Q q a y : ℂ)) (Set.Icc (s 0) (s N)) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_primeLogDensity _ _ _ (by linarith))
  rwa [(rootMeshWeight_integral F w S hconst s hs N hfree _ hρ).2] at h

theorem common_root_integer_integral
    (S : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (q a : ℕ) (hq : 0 < q) (G : ℝ) {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexIntegerInterval q a (s 0) (s N) G
        (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc (s 0) (s N), w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
        (integerLogDensity q G y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (2 * Real.exp (-G)) + 2 * C * smoothPolynomialBudget F * Real.exp (-G)) := by
  have h := common_root_mesh_integer_comparison S s hs N hfree q a hq G F hroots w C hC hw hconst
  have hρ : ContinuousOn (fun y => (integerLogDensity q G y : ℂ)) (Set.Icc (s 0) (s N)) :=
    (Complex.continuous_ofReal.comp (continuous_integerLogDensity q G)).continuousOn
  rwa [(rootMeshWeight_integral F w S hconst s hs N hfree _ hρ).2] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealSmooth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single real smooth kernel for the two original giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem MovingSlotReversal.continuous_realPivot {σ : Type*}
    (value : σ → ℕ) (s : MovingSlotReversal σ) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => s.realPivot value (L x) (R x)) := by
  unfold realPivot
  exact ((continuous_const.mul hR).sub (continuous_const.mul hL)).div_const _

theorem MovingSlotData.continuous_realLeafModuli {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) (i : TreeLeafIndex n) :
    Continuous (fun x => T.realLeafModuli value (L x) (R x) i) := by
  induction T generalizing L R with
  | leaf => exact (hL.mul hR).mul_const _
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).continuous_realPivot value L R hL hR
    cases i with
    | inl i => exact ihL _ L hp hL i
    | inr i => exact ihR _ R hp hR i

theorem movingFourierPolynomialFactors_real {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (z : ℝ) :
    smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z =
      movingRealFourierWeight value T ψ X lo hi hlo hhi (L.eval z) (R.eval z) := by
  unfold smoothPolynomialWeight movingRealFourierWeight
  rw [← (movingLeafIndexEquiv n).prod_comp
    (fun j => (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi j).value z)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [movingFourierPolynomialFactors, Equiv.symm_apply_apply]
  split_ifs <;>
    simp only [ClippedPolynomialFactor.conjugate, ClippedPolynomialFactor.value,
      fourierPolynomialFactor, movingLeafNormalizedPolynomial_eval, T.leafPolynomials_real,
      Polynomial.eval_X]

theorem continuous_movingRealFourierWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealFourierWeight value T ψ X lo hi hlo hhi (L x) (R x)) := by
  apply continuous_finsetProd
  intro i _
  have hc := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).continuous_value.comp
    ((T.continuous_realLeafModuli value L R hL hR i).div_const X)
  dsimp only
  split_ifs
  · exact Complex.continuous_conj.comp hc
  · exact hc

theorem continuous_movingRealNodeCutoff {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealNodeCutoff value φ G T (L x) (R x)) := by
  have hp (g : ℝ) : Continuous (fun x => (positiveLogCutoff φ g x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ g B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ g B D hB hD hφ hlip).continuous_value).congr he
  induction T generalizing L R with
  | leaf => exact continuous_const
  | @node n s CL CR u left right ihL ihR =>
    have hc := (MovingSlotData.step s CL CR u left right false).continuous_realPivot value L R hL hR
    exact (((hp (G (n + 1))).comp hc).mul (ihL _ L hc hL)).mul (ihR _ R hc hR)

theorem movingSmoothPolynomialFactors_real {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip) z =
        movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G (L.eval z) (R.eval z) := by
  rw [movingSmoothPolynomialFactors_value value T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout,
    movingFourierPolynomialFactors_real]
  rfl

theorem continuous_movingRealSmoothWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {A : Type*} [TopologicalSpace A] (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G (L x) (R x)) :=
  (continuous_movingRealFourierWeight value T ψ X lo hi hlo hhi L R hL hR).mul
    (continuous_movingRealNodeCutoff value φ G B D hB hD hφ hlip hout T L R hL hR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability and uniform bounds for the original two-giant kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap
open MeasureTheory

theorem HistoryFormula.continuous_realEval {σ : Type*} (F : HistoryFormula σ) :
    Continuous F.realEval := by
  unfold realEval
  simp only [MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.continuous_eval _).div_const _

theorem WordTransferGuard.isClosed_archimedeanAt {σ : Type*} (g : WordTransferGuard σ) :
    IsClosed {x | g.archimedeanAt x} :=
  (isClosed_le continuous_const g.pivot.continuous_realEval).inter
    ((isClosed_le g.pivot.continuous_realEval continuous_const).inter
      (isClosed_le continuous_const g.rightProduct.continuous_realEval))

theorem isClosed_movingArchimedeanGate (nodes : List MovingFormulaNode) :
    IsClosed {x | movingArchimedeanGate nodes x} := by
  induction nodes with
  | nil => simpa only [movingArchimedeanGate, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, Set.ofPred_true] using isClosed_univ
  | cons f nodes ih =>
    simpa only [movingArchimedeanGate, List.forall_mem_cons, Set.ofPred_and] using
      f.guard.isClosed_archimedeanAt.inter ih

theorem continuous_topGiantReal : Continuous (fun x : ℝ × ℝ => topGiantReal x.1 x.2) := by
  apply continuous_pi
  intro b
  cases b
  · exact continuous_fst
  · exact continuous_snd

theorem measurable_movingRealGateWeight {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ) :
    Measurable (fun x : ℝ × ℝ => movingRealGateWeight value T nodes X lo hi (topGiantReal x.1 x.2)) := by
  have ha : Measurable (fun x : ℝ × ℝ => movingArchimedeanFlag nodes (topGiantReal x.1 x.2)) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact ((isClosed_movingArchimedeanGate nodes).preimage continuous_topGiantReal).measurableSet
  have hw : Measurable (fun x : ℝ × ℝ => movingRealWindowFlag value T X lo hi x.1 x.2) := by
    apply Measurable.ite _ measurable_const measurable_const
    have hc : IsClosed {x : ℝ × ℝ | ∀ i, T.realLeafModuli value x.1 x.2 i / X ∈ Set.Icc lo hi} := by
      simpa only [Set.ofPred_forall, Set.preimage] using isClosed_iInter (fun i : TreeLeafIndex n =>
        isClosed_Icc.preimage ((T.continuous_realLeafModuli value Prod.fst Prod.snd
          continuous_fst continuous_snd i).div_const X))
    exact hc.measurableSet
  exact ha.mul hw

theorem movingRealFourierWeight_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (L R : ℝ) :
    ‖movingRealFourierWeight value T ψ X lo hi hlo hhi L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) := by
  have he : (SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) =
      ∏ _i : TreeLeafIndex n, SchwartzMap.seminorm ℝ 0 0 ψ := by
    simp only [Finset.prod_const, Finset.card_univ, card_treeLeafIndex]
  rw [he, movingRealFourierWeight, norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i _
  have hb := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).norm_value
    (T.realLeafModuli value L R i / X)
  change ‖(fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).value
    (T.realLeafModuli value L R i / X)‖ ≤ SchwartzMap.seminorm ℝ 0 0 ψ at hb
  split_ifs
  · simpa only [Complex.norm_conj] using hb
  · exact hb

theorem movingRealNodeCutoff_norm {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) :
    ‖movingRealNodeCutoff value φ G T L R‖ ≤ B ^ (2 ^ n - 1) := by
  have hb (G x : ℝ) : ‖(positiveLogCutoff φ G x : ℂ)‖ ≤ B := by
    unfold positiveLogCutoff
    split_ifs
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hφ _
    · simpa only [Complex.ofReal_zero, norm_zero] using hB
  induction T generalizing L R with
  | leaf => simp [movingRealNodeCutoff]
  | @node n s CL CR u left right ihL ihR =>
    simp only [movingRealNodeCutoff, norm_mul]
    calc
      _ ≤ (B * B ^ (2 ^ n - 1)) * B ^ (2 ^ n - 1) := by
        apply mul_le_mul _ (ihR _ _) (norm_nonneg _) (mul_nonneg hB (pow_nonneg hB _))
        exact mul_le_mul (hb _ _) (ihL _ _) (norm_nonneg _) hB
      _ = B ^ (2 ^ (n + 1) - 1) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        have := Nat.one_le_two_pow (n := n)
        rw [pow_succ]
        omega

theorem movingRealSmoothWeight_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1) := by
  rw [movingRealSmoothWeight, norm_mul]
  exact mul_le_mul (movingRealFourierWeight_norm value T ψ X lo hi hlo hhi L R)
    (movingRealNodeCutoff_norm value φ G B hB hφ T L R) (norm_nonneg _)
    (pow_nonneg ((norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)) _)

theorem measurable_movingRealKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    Measurable (fun x : ℝ × ℝ => movingRealKernel value T nodes ψ X lo hi hlo hhi φ G x.1 x.2) :=
  (measurable_movingRealGateWeight value T nodes X lo hi).mul
    (continuous_movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      Prod.fst Prod.snd continuous_fst continuous_snd).measurable

theorem movingRealKernel_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖movingRealKernel value T nodes ψ X lo hi hlo hhi φ G L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1) := by
  rw [movingRealKernel, norm_mul]
  exact (mul_le_mul_of_nonneg_right (movingRealGateWeight_norm value T nodes X lo hi _)
    (norm_nonneg _)).trans (by simpa only [one_mul] using
      movingRealSmoothWeight_norm value T ψ X lo hi hlo hhi φ G B hB hφ L R)

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

/-- The giant row of Section 8.2 absorbs all fixed-depth variation,
normalization and residue-count costs. The threshold precedes every modulus,
endpoint and weight budget. -/
theorem PublishedProgressionInput.weighted_giant_budget_rate (P : PublishedProgressionInput)
    (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u V : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u →
      V ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) ≤
          Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by
  filter_upwards [P.log_interval_budget_rate (49 / 1000) (12 / 1000) (18 / 1000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_error_absorption (12 / 1000) (18 / 1000) (14 / 1000) C 1 d
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    constant_mul_double_exp_le 2 1 (14 / 1000) (13 / 1000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with L hE hcost htwo
  intro Q hQ hlog u V hu hV
  have hnonneg : 0 ≤ 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
      Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.errorConstant_nonneg)
      (Real.exp_pos _).le) (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) *
        (2 * Real.exp (-Real.exp ((18 / 1000 : ℝ) * L))) :=
      mul_le_mul hV (hE Q hQ hlog u hu) hnonneg (Real.exp_pos _).le
    _ = 2 * (Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) *
        Real.exp (-Real.exp ((18 / 1000 : ℝ) * L))) := by ring
    _ ≤ 2 * Real.exp (-Real.exp ((14 / 1000 : ℝ) * L)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [neg_mul, one_mul] using hcost
    _ ≤ _ := by simpa only [neg_mul, one_mul] using htwo

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RootCellErrorRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete root-cell error retains a double-exponential saving -/

namespace Ostmann
open Filter
open scoped BigOperators
open MeasureTheory

theorem weighted_giant_atom_rate (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ u B : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u →
      B ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      B * Real.exp (-u) ≤ Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by
  filter_upwards [arithmetic_error_absorption (12 / 1000) (49 / 1000) (13 / 1000) C 1 d
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with L hL
  intro u B hu hB
  calc
    _ ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
    _ ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) *
        Real.exp (-Real.exp ((49 / 1000 : ℝ) * L)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hu)) (Real.exp_pos _).le
    _ ≤ _ := by simpa only [one_mul, neg_mul] using hL

/-- The number of root cells is fixed before X grows. This estimate includes
both the weighted progression error and all retained endpoint-prime atoms. -/
theorem PublishedProgressionInput.root_cell_error_rate (P : PublishedProgressionInput)
    (C : ℝ) (d K : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ N : ℕ, N ≤ K → ∀ s V B : ℕ → ℝ,
      (∀ j < N, Real.exp ((49 / 1000 : ℝ) * L) ≤ s j) →
      (∀ j < N, V j ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      (∀ j < N, B j ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      (∑ j ∈ Finset.range N,
        (V j * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
          Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) + B j * Real.exp (-(s j)))) ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.weighted_giant_budget_rate C d, weighted_giant_atom_rate C d,
    constant_mul_double_exp_le (2 * (K : ℝ)) 1 (13 / 1000) (125 / 10000)
      (by positivity) (by norm_num) (by norm_num) (by norm_num)] with L hP hA hK
  intro Q hQ hlog N hNK s V B hs hV hB
  calc
    _ ≤ ∑ _j ∈ Finset.range N, 2 * Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN := Finset.mem_range.mp hj
      linarith [hP Q hQ hlog (s j) (V j) (hs j hjN) (hV j hjN),
        hA (s j) (B j) (hs j hjN) (hB j hjN)]
    _ = 2 * (N : ℝ) * Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by simp; ring
    _ ≤ 2 * (K : ℝ) * Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by
      gcongr
    _ ≤ _ := by simpa only [one_mul, neg_mul] using hK

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RootIntegralRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform rates for the whole sharp-gate integral -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators

theorem PublishedProgressionInput.root_integral_prime_rate (P : PublishedProgressionInput)
    (C : ℝ) (d K : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q q a : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      ∀ (k : ℕ) (F : Fin k → ClippedPolynomialFactor) (S : Finset ℝ), S.card + 1 ≤ K →
      (∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S) →
      ∀ (w : ℝ → ℂ) (B : ℝ), 0 ≤ B → (∀ x, ‖w x‖ ≤ B) →
      (∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) →
      2 * B * smoothPolynomialBudget F ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexPrimeInterval q a u v (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
        ∫ y in Set.Ioc u v, w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
          (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.root_cell_error_rate C d K, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro Q q a hQ hq hqQ ha hlog u v hu huv hshort k F S hSK hroots w B hB hw hconst hbudget
  obtain ⟨s, N, hs, hs0, hsN, hN, hfree⟩ := finite_log_root_mesh S u v huv
  have hu1 : 1 ≤ s 0 := by rw [hs0]; exact (Real.one_le_exp (by positivity)).trans hu
  have h := P.common_root_prime_integral S s hs N hfree hQ hq hqQ ha hu1
    (by simpa only [hs0, hsN] using hshort) F hroots w B hB hw hconst
  rw [hs0, hsN] at h
  apply h.trans
  apply hL Q hQ hlog N (hN.trans hSK) s
    (fun j => ‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F)
    (fun _ => 2 * B * smoothPolynomialBudget F)
  · intro j _
    exact hu.trans (by rw [← hs0]; exact hs (Nat.zero_le _))
  · intro j _
    have hbF := mul_le_mul_of_nonneg_right (hw (Real.exp ((s j + s (j + 1)) / 2)))
      (smoothPolynomialBudget_nonneg F)
    have hBF : 0 ≤ B * smoothPolynomialBudget F := mul_nonneg hB (smoothPolynomialBudget_nonneg F)
    nlinarith
  · intro j _
    exact hbudget

theorem root_integral_integer_bound (q a : ℕ) (hq : 0 < q) (u v G : ℝ) (huv : u ≤ v)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) (S : Finset ℝ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ x, ‖w x‖ ≤ B)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexIntegerInterval q a u v G (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc u v, w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
        (integerLogDensity q G y : ℂ)‖ ≤
      4 * ((S.card + 1 : ℕ) : ℝ) * B * smoothPolynomialBudget F * Real.exp (-G) := by
  obtain ⟨s, N, hs, hs0, hsN, hN, hfree⟩ := finite_log_root_mesh S u v huv
  have h := common_root_integer_integral S s hs N hfree q a hq G F hroots w B hB hw hconst
  rw [hs0, hsN] at h
  apply h.trans
  calc
    _ ≤ ∑ _j ∈ Finset.range N, 4 * B * smoothPolynomialBudget F * Real.exp (-G) := by
      apply Finset.sum_le_sum
      intro j _
      have hbF := mul_le_mul_of_nonneg_right (hw (Real.exp ((s j + s (j + 1)) / 2)))
        (smoothPolynomialBudget_nonneg F)
      have he := mul_le_mul_of_nonneg_right hbF (by positivity : 0 ≤ 2 * Real.exp (-G))
      nlinarith
    _ = (N : ℝ) * (4 * B * smoothPolynomialBudget F * Real.exp (-G)) := by simp
    _ ≤ ((S.card + 1 : ℕ) : ℝ) * (4 * B * smoothPolynomialBudget F * Real.exp (-G)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hN)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hB)
        (smoothPolynomialBudget_nonneg F)) (Real.exp_pos _).le
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelSlices
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete polynomial data for either slice of the two-giant kernel -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingSmoothPolynomialFactors_root_data {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    ∃ S : Finset ℝ, S.card ≤ 2 ^ n ∧ ∀ i r,
      r ∈ ((movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
        φ G B D hB hD hφ hlip i).polynomial.derivative).roots → r ∈ S := by
  let F := movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi
  let S := polynomialRootCuts (fun i => (F i).polynomial.derivative)
  have hdeg (i : Fin (2 ^ n)) : (F i).polynomial.derivative.natDegree ≤ 1 := by
    have h := movingFourierPolynomialFactors_degree value T L R ψ X lo hi hlo hhi hL hR i
    change (F i).polynomial.natDegree ≤ 2 at h
    exact (Polynomial.natDegree_derivative_le _).trans (by omega)
  refine ⟨S, ?_, ?_⟩
  · exact (polynomialRootCuts_card _).trans (by
      calc
        _ ≤ ∑ _i : Fin (2 ^ n), 1 := Finset.sum_le_sum (fun i _ => hdeg i)
        _ = _ := by simp)
  · intro i r
    refine Fin.addCases ?_ ?_ i
    · intro j hr
      simp only [movingSmoothPolynomialFactors, Fin.append_left] at hr
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩
    · intro j
      simp only [movingSmoothPolynomialFactors, Fin.append_right]
      rw [movingNodeCutoffFactors_no_derivative_roots value T L R hL hR φ G B D hB hD hφ hlip j]
      simp

theorem movingRealKernel_slice_polynomial {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (coord : Bool) (fixed z : ℝ) :
    movingRealKernel value T nodes ψ X lo hi hlo hhi φ G
      (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) =
      movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed z) *
        smoothPolynomialWeight (movingSmoothPolynomialFactors value T
          (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
          ψ X lo hi hlo hhi φ G B D hB hD hφ hlip) z := by
  rw [movingSmoothPolynomialFactors_real value T _ _ ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout,
    (movingCoordinate_eval coord fixed z).1, (movingCoordinate_eval coord fixed z).2]
  unfold movingRealKernel
  congr 2
  funext b
  cases coord <;> cases b <;> rfl

/-- The root count is uniform in both real coordinate values and all fixed
small primes. This is the certificate used by the joint giant comparison. -/
theorem movingRealKernel_slice_root_data {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (coord : Bool) (fixed : ℝ) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    let W := movingSmoothPolynomialFactors value T
      (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    ∃ S : Finset ℝ,
      S.card ≤ (2 ^ n - 1) * (3 * (7 * 2 ^ n)) + 5 * 2 ^ n ∧
      (∀ i r, r ∈ (W i).polynomial.derivative.roots → r ∈ S) ∧
      (∀ x y, rootCellCode S x = rootCellCode S y →
        movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed x) =
        movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed y)) := by
  dsimp only
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  obtain ⟨S, hS, hroot⟩ := movingSmoothPolynomialFactors_root_data value T
    (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
    (by cases coord <;> simp [movingCoordinateLeft])
    (by cases coord <;> simp [movingCoordinateRight]) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
  refine ⟨movingRealRootCuts value T nodes X lo hi coord fixed ∪ S, ?_, ?_, ?_⟩
  · have ha := movingRealRootCuts_card value hvalue childBound pivotBound T hf X lo hi coord fixed
    exact (Finset.card_union_le _ _).trans (by dsimp only [nodes]; omega)
  · intro i r hr
    exact Finset.mem_union_right _ (hroot i r hr)
  · intro x y hcode
    exact movingRealGateWeight_rootCell value T nodes X lo hi coord fixed x y _
      Finset.subset_union_left hcode

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal product of the two histories in a diagonal comparison -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem pairedPolynomialFactors_roots {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (S U : Finset ℝ)
    (hS : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (hU : ∀ i r, r ∈ (G i).polynomial.derivative.roots → r ∈ U) :
    ∀ i r, r ∈ ((pairedPolynomialFactors F G) i).polynomial.derivative.roots → r ∈ S ∪ U := by
  intro i r
  refine Fin.addCases ?_ ?_ i
  · intro j hr
    simp only [pairedPolynomialFactors, Fin.append_left] at hr
    exact Finset.mem_union_left _ (hS j r hr)
  · intro j hr
    simp only [pairedPolynomialFactors, Fin.append_right, ClippedPolynomialFactor.conjugate] at hr
    exact Finset.mem_union_right _ (hU j r hr)

theorem movingPairedSmoothPolynomialFactors_budget {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (pairedPolynomialFactors
      (movingSmoothPolynomialFactors value (T false) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
      (movingSmoothPolynomialFactors value (T true) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)) ≤
      (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  rw [pairedPolynomialFactors_budget, pow_two]
  have h0 := movingSmoothPolynomialFactors_budget value (T false) L R ψ X lo hi V hlo hhi
    (hV false) φ G B D hB hD hφ hlip
  have h1 := movingSmoothPolynomialFactors_budget value (T true) L R ψ X lo hi V hlo hhi
    (hV true) φ G B D hB hD hφ hlip
  exact mul_le_mul h0 h1 (smoothPolynomialBudget_nonneg _) ((smoothPolynomialBudget_nonneg _).trans h0)

theorem movingRealKernelPair_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G L R‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 := by
  rw [movingRealKernelPair, norm_mul, Complex.norm_conj, pow_two]
  exact mul_le_mul
    (movingRealKernel_norm value (T false) (nodes false) ψ X lo hi hlo hhi φ G B hB hφ L R)
    (movingRealKernel_norm value (T true) (nodes true) ψ X lo hi hlo hhi φ G B hB hφ L R)
    (norm_nonneg _) (by positivity)

theorem measurable_movingRealKernelPair {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    Measurable (fun z : ℝ × ℝ => movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G z.1 z.2) := by
  have h0 := measurable_movingRealKernel value (T false) (nodes false) ψ X lo hi hlo hhi φ G
    B D hB hD hφ hlip hout
  have h1 := measurable_movingRealKernel value (T true) (nodes true) ψ X lo hi hlo hhi φ G
    B D hB hD hφ hlip hout
  exact h0.mul (Complex.continuous_conj.measurable.comp h1)

theorem movingRealKernelPair_slice_polynomial {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (coord : Bool) (fixed z : ℝ) :
    let W := fun b => movingSmoothPolynomialFactors value (T b)
      (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
      (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) =
      (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed z) *
        conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed z))) *
        smoothPolynomialWeight (pairedPolynomialFactors (W false) (W true)) z := by
  dsimp only
  rw [movingRealKernelPair,
    movingRealKernel_slice_polynomial value (T false) (nodes false) ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip hout,
    movingRealKernel_slice_polynomial value (T true) (nodes true) ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip hout,
    pairedPolynomialFactors_weight, map_mul]
  ring

theorem movingRealKernelPair_slice_root_data {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (coord : Bool) (fixed : ℝ) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    let W := fun b => movingSmoothPolynomialFactors value (T b)
      (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    ∃ S : Finset ℝ, S.card + 1 ≤ 2 * movingKernelRootBudget n ∧
      (∀ i r, r ∈ ((pairedPolynomialFactors (W false) (W true)) i).polynomial.derivative.roots → r ∈ S) ∧
      (∀ x y, rootCellCode S x = rootCellCode S y →
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))) =
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed y) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed y)))) := by
  dsimp only
  obtain ⟨S, hS, hSr, hSc⟩ := movingRealKernel_slice_root_data value hvalue childBound pivotBound
    (T false) (hf false) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  obtain ⟨U, hU, hUr, hUc⟩ := movingRealKernel_slice_root_data value hvalue childBound pivotBound
    (T true) (hf true) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  refine ⟨S ∪ U, ?_, pairedPolynomialFactors_roots _ _ S U hSr hUr, ?_⟩
  · have hc := Finset.card_union_le S U
    unfold movingKernelRootBudget
    omega
  · intro x y hc
    rw [hSc x y (rootCellCode_eq_of_subset S (S ∪ U) Finset.subset_union_left x y hc),
      hUc x y (rootCellCode_eq_of_subset U (S ∪ U) Finset.subset_union_right x y hc)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingIntegerPairRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform integer comparison for a literal moving-kernel slice -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical SchwartzMap

theorem moving_pair_integer_error_rate (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ J A : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J →
      A ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      4 * (movingKernelRootBudget n : ℝ) * A * Real.exp (-J) ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [weighted_giant_atom_rate C d,
    constant_mul_double_exp_le (4 * (movingKernelRootBudget n : ℝ)) 1
      (13 / 1000) (125 / 10000) (by positivity) (by norm_num) (by norm_num) (by norm_num)]
    with L hA hK
  intro J A hJ hbudget
  calc
    _ = 4 * (movingKernelRootBudget n : ℝ) * (A * Real.exp (-J)) := by ring
    _ ≤ 4 * (movingKernelRootBudget n : ℝ) * Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) :=
      mul_le_mul_of_nonneg_left (hA J A hJ hbudget) (by positivity)
    _ ≤ _ := by simpa only [one_mul, neg_mul] using hK

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

theorem intervalDensityMeasure_integral (u v : ℝ) (ρ : ℝ → ℝ)
    (hρ : AEMeasurable ρ (volume.restrict (Set.Ioc u v)))
    (hpos : ∀ x ∈ Set.Ioc u v, 0 ≤ ρ x) (f : ℝ → ℂ) :
    (∫ x, f x ∂intervalDensityMeasure u v ρ) =
      ∫ x in Set.Ioc u v, f x * (ρ x : ℂ) := by
  unfold intervalDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ hρ.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [ENNReal.toReal_ofReal (hpos x hx), Complex.real_smul, mul_comm]

theorem intervalDensityMeasure_mass (u v : ℝ) (ρ : ℝ → ℝ)
    (hρ : IntegrableOn ρ (Set.Ioc u v)) (hpos : ∀ x ∈ Set.Ioc u v, 0 ≤ ρ x) :
    (intervalDensityMeasure u v ρ).real Set.univ = ∫ x in Set.Ioc u v, ρ x := by
  have hp : ∀ᵐ x ∂volume.restrict (Set.Ioc u v), 0 ≤ ρ x :=
    ae_restrict_of_forall_mem measurableSet_Ioc hpos
  rw [Measure.real, intervalDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hρ hp,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hp)]

theorem measurable_selectedPrimeLogDensity (P : PublishedProgressionInput) (Q q a : ℕ) :
    Measurable (selectedPrimeLogDensity P Q q a) := by
  unfold selectedPrimeLogDensity primeLogDensity
  fun_prop

theorem primeGiantMeasure_integral (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 ≤ u) (f : ℝ → ℂ) :
    (∫ x, f x ∂primeGiantMeasure P Q q a u v) =
      ∫ x in Set.Ioc u v, f x * (selectedPrimeLogDensity P Q q a x : ℂ) :=
  intervalDensityMeasure_integral u v _ (measurable_selectedPrimeLogDensity P Q q a).aemeasurable
    (selectedPrimeLogDensity_nonneg P Q q a u v hu) f

theorem finite_integerGiantMeasure (q : ℕ) (G u v : ℝ) :
    IsFiniteMeasure (integerGiantMeasure q G u v) :=
  finite_intervalDensityMeasure u v _
    ((continuous_integerLogDensity q G).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (by intro x _; unfold integerLogDensity; positivity)

theorem integerGiantMeasure_integral (q : ℕ) (G u v : ℝ) (f : ℝ → ℂ) :
    (∫ x, f x ∂integerGiantMeasure q G u v) =
      ∫ x in Set.Ioc u v, f x * (integerLogDensity q G x : ℂ) :=
  intervalDensityMeasure_integral u v _ (continuous_integerLogDensity q G).measurable.aemeasurable
    (by intro x _; unfold integerLogDensity; positivity) f

theorem integerGiantMeasure_mass_le (q : ℕ) (hq : 0 < q) (J u v : ℝ)
    (huv : u ≤ v) (hshort : v ≤ u + 1) :
    (integerGiantMeasure q J u v).real Set.univ ≤ Real.exp (v - J) := by
  rw [integerGiantMeasure, intervalDensityMeasure_mass u v _
    ((continuous_integerLogDensity q J).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (by intro x _; unfold integerLogDensity; positivity)]
  exact (le_abs_self _).trans (integerLogDensity_integral_abs_le q hq u v J huv hshort)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TwoGiantIntegralTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint transport of the two original giant coordinates -/

namespace Ostmann
open scoped BigOperators
open MeasureTheory

/-- Slice comparisons combine against the original outer prior and the
ideal inner measure. This introduces neither conditional sampling nor a
count of real partition boxes. -/
theorem two_giant_integral_transport {A B X Y : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace X] [MeasurableSpace Y]
    (α : A → ℝ) (β : B → ℝ) (x : A → X) (y : B → Y)
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) (H : X → Y → ℂ)
    (hβ : ∀ b, 0 ≤ β b) (δ ε : ℝ)
    (hH : ∀ b, Integrable (fun z => H z (y b)) μ)
    (hI : Integrable (fun z => ∫ t, H z t ∂ν) μ)
    (hleft : ∀ b, ‖(∑ a, (α a : ℂ) * H (x a) (y b)) - ∫ z, H z (y b) ∂μ‖ ≤ δ)
    (hright : ∀ᵐ z ∂μ, ‖(∑ b, (β b : ℂ) * H z (y b)) - ∫ t, H z t ∂ν‖ ≤ ε) :
    ‖(∑ b, (β b : ℂ) * ∑ a, (α a : ℂ) * H (x a) (y b)) -
      ∫ z, ∫ t, H z t ∂ν ∂μ‖ ≤ δ * (∑ b, β b) + ε * μ.real Set.univ := by
  let Z := ∑ b, (β b : ℂ) * ∫ z, H z (y b) ∂μ
  have h1 : ‖(∑ b, (β b : ℂ) * ∑ a, (α a : ℂ) * H (x a) (y b)) - Z‖ ≤
      δ * (∑ b, β b) := by
    dsimp only [Z]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      _ ≤ ∑ b, ‖(β b : ℂ) * ((∑ a, (α a : ℂ) * H (x a) (y b)) -
          ∫ z, H z (y b) ∂μ)‖ := norm_sum_le _ _
      _ ≤ ∑ b, β b * δ := by
        apply Finset.sum_le_sum
        intro b _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ b)]
        exact mul_le_mul_of_nonneg_left (hleft b) (hβ b)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hint : Integrable (fun z => ∑ b, (β b : ℂ) * H z (y b)) μ :=
    integrable_finsetSum _ (fun b _ => (hH b).const_mul _)
  have hZ : Z = ∫ z, ∑ b, (β b : ℂ) * H z (y b) ∂μ := by
    rw [integral_finsetSum _ (fun b _ => (hH b).const_mul _)]
    simp only [integral_const_mul, Z]
  have h2 : ‖Z - ∫ z, ∫ t, H z t ∂ν ∂μ‖ ≤ ε * μ.real Set.univ := by
    rw [hZ, ← integral_sub hint hI]
    exact norm_integral_le_of_norm_le_const hright
  exact (norm_sub_le_norm_sub_add_norm_sub _ Z _).trans (add_le_add h1 h2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantDiscreteTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint transport of the literal reciprocal-prime and integer sums -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

theorem primeResidueAtom_nonneg (q a p : ℕ) : 0 ≤ primeResidueAtom q a p := by
  unfold primeResidueAtom
  split_ifs <;> positivity

theorem complexPrimeInterval_subtype (q a : ℕ) (u v : ℝ) (f : ℝ → ℂ) :
    complexPrimeInterval q a u v f =
      ∑ p : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
        (primeResidueAtom q a p : ℂ) * f (Real.log (p : ℕ)) := by
  rw [Finset.sum_coe_sort (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊)
    (fun p : ℕ => (primeResidueAtom q a p : ℂ) * f (Real.log p))]
  unfold complexPrimeInterval primeResidueAtom
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp only [Complex.ofReal_zero, Complex.ofReal_inv, zero_mul, mul_comm]

theorem complexIntegerInterval_subtype (q a : ℕ) (u v G : ℝ) (f : ℝ → ℂ) :
    complexIntegerInterval q a u v G f =
      ∑ p : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
        (integerResidueAtom q a G p : ℂ) * f (Real.log (p : ℕ)) := by
  rw [Finset.sum_coe_sort (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊)
    (fun p : ℕ => (integerResidueAtom q a G p : ℂ) * f (Real.log p))]
  unfold complexIntegerInterval
  apply Finset.sum_congr rfl
  intro p _
  exact mul_comm _ _

theorem primeResidueAtom_subtype_mass (q a : ℕ) (u v : ℝ) :
    (∑ p : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, primeResidueAtom q a p) =
      reciprocalPrimeInterval q a (Real.exp u) (Real.exp v) := by
  rw [Finset.sum_coe_sort]
  rfl

theorem mixed_pair_integral_transport (q a b : ℕ) (u v r s G : ℝ)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H))
    (K : ℝ) (hK : ∀ x y, ‖H x y‖ ≤ K) (δ ε : ℝ)
    (hleft : ∀ y, ‖complexIntegerInterval q a u v G (fun x => H x y) - ∫ x, H x y ∂μ‖ ≤ δ)
    (hright : ∀ x, ‖complexPrimeInterval q b r s (H x) - ∫ y, H x y ∂ν‖ ≤ ε) :
    ‖complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v G (fun x => H x y)) -
      ∫ x, ∫ y, H x y ∂ν ∂μ‖ ≤
      δ * reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + ε * μ.real Set.univ := by
  have hp : Integrable (Function.uncurry H) (μ.prod ν) :=
    ⟨hH.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun z => hK z.1 z.2)⟩
  have hs (y : ℝ) : Integrable (fun x => H x y) μ :=
    ⟨(hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun x => hK x y)⟩
  have h := two_giant_integral_transport
    (fun p : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊ => integerResidueAtom q a G p)
    (fun p : Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊ => primeResidueAtom q b p)
    (fun p => Real.log (p : ℕ)) (fun p => Real.log (p : ℕ)) μ ν H
    (fun p => primeResidueAtom_nonneg q b p) δ ε (fun p => hs (Real.log (p : ℕ)))
    hp.integral_prod_left (by intro p; simpa only [complexIntegerInterval_subtype] using hleft (Real.log (p : ℕ)))
    (Filter.Eventually.of_forall fun x => by simpa only [complexPrimeInterval_subtype] using hright x)
  simpa only [complexPrimeInterval_subtype, complexIntegerInterval_subtype,
    primeResidueAtom_subtype_mass] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measure transport for the concrete bounded moving kernel -/

namespace Ostmann
open MeasureTheory
open scoped Classical SchwartzMap

theorem measurable_exp_pair_mul (K : ℝ → ℝ → ℂ)
    (hK : Measurable (Function.uncurry K)) (c : ℂ) :
    Measurable (Function.uncurry (fun x y => c * K (Real.exp x) (Real.exp y))) := by
  have he : Measurable (fun z : ℝ × ℝ => (Real.exp z.1, Real.exp z.2)) :=
    (Real.continuous_exp.comp continuous_fst).measurable.prodMk
      (Real.continuous_exp.comp continuous_snd).measurable
  exact measurable_const.mul (hK.comp he)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ReciprocalPolynomialFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized counterpart ratio is an admissible smooth factor -/

namespace Ostmann

open scoped BigOperators

theorem reciprocalPolynomialFactor_original (P : Polynomial ℝ) (hi : ℝ)
    (hhi : 1 ≤ hi) (x X M : ℝ) (hX : X ≠ 0) (hM : M ≠ 0)
    (hP : P.eval x = M / X) (hrange : M / X ∈ Set.Icc (1 : ℝ) hi) :
    (reciprocalPolynomialFactor P hi hhi).value x = Complex.ofReal (X / M) := by
  rw [ClippedPolynomialFactor.value_of_mem _ x (by
    change P.eval x ∈ Set.Icc (1 : ℝ) hi
    rw [hP]
    exact hrange)]
  change Complex.ofReal ((P.eval x)⁻¹) = _
  rw [hP]
  congr 1
  field_simp

theorem reciprocalPolynomialFactor_budget (P : Polynomial ℝ) (hi : ℝ) (hhi : 1 ≤ hi) :
    2 * (reciprocalPolynomialFactor P hi hhi).bound +
      (reciprocalPolynomialFactor P hi hhi).lip *
        ((reciprocalPolynomialFactor P hi hhi).hi - (reciprocalPolynomialFactor P hi hhi).lo) =
      hi + 1 := by
  dsimp only [reciprocalPolynomialFactor]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantReciprocalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized reciprocal giant factor in the diagonal multiplier -/

namespace Ostmann

theorem giantReciprocalFactor_budget (P : Polynomial ℝ) (G : ℝ) :
    2 * (giantReciprocalFactor P G).bound + (giantReciprocalFactor P G).lip *
      ((giantReciprocalFactor P G).hi - (giantReciprocalFactor P G).lo) = 1 + Real.exp 2 := by
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_budget, add_comm]

theorem giantReciprocalFactor_value (P : Polynomial ℝ) (G x : ℝ)
    (hx : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1))) :
    (Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x = (Real.exp G / P.eval x : ℝ) := by
  have hlo : 0 < Real.exp (G - 1) := Real.exp_pos _
  have hp : 0 < P.eval x := hlo.trans_le hx.1
  have hrange : P.eval x / Real.exp (G - 1) ∈ Set.Icc (1 : ℝ) (Real.exp 2) := by
    refine ⟨(one_le_div hlo).mpr hx.1, ?_⟩
    calc
      _ ≤ Real.exp (G + 1) / Real.exp (G - 1) := div_le_div_of_nonneg_right hx.2 hlo.le
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_original _ _ _ x
    (Real.exp (G - 1)) (P.eval x) hlo.ne' hp.ne'
    (by simp only [Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv, mul_comm]) hrange,
    ← Complex.ofReal_mul]
  apply congrArg (fun a : ℝ => (a : ℂ))
  rw [← mul_div_assoc, ← Real.exp_add, show 1 + (G - 1) = G by ring]

/-- Multiplication by the actual giant cutoff makes the clipped reciprocal
identical to the manuscript's reciprocal everywhere, including zero terms. -/
theorem giantReciprocalFactor_cutoff (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    (logCutoffPolynomialFactor P φ G B D hB hD hφ hlip).value x *
      ((Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x) =
        (positiveLogCutoff φ G (P.eval x) : ℂ) * (Real.exp G / P.eval x : ℝ) := by
  rw [logCutoffPolynomialFactor_value P φ G B D hB hD hφ hlip hout x]
  by_cases hz : positiveLogCutoff φ G (P.eval x) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · have hx : 0 < P.eval x := by
      by_contra hn
      exact hz (by simp only [positiveLogCutoff, ite_eq_right hn])
    have hn : φ (Real.log (P.eval x) - G) ≠ 0 := by
      simpa only [positiveLogCutoff, ite_eq_left hx] using hz
    have hr : |Real.log (P.eval x) - G| < 1 := lt_of_not_ge (fun h => hn (hout _ h))
    have hbounds : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1)) := by
      have h := abs_lt.mp hr
      constructor
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
    rw [giantReciprocalFactor_value P G x hbounds]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantOuterFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two outer cutoff priors and the diagonal reciprocal factor -/

namespace Ostmann
open scoped BigOperators Classical

/-- Both actual cutoff priors are retained. In the diagonal environment the
remaining factor is precisely exp(G_R)/R, including all off-support zeros. -/
theorem giantOuterFactors_value (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    (giantOuterScalar diagonal : ℂ) *
      smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x =
        (positiveLogCutoff φ Jleft (L.eval x) : ℂ) * (positiveLogCutoff φ Jright (R.eval x) : ℂ) *
          (if diagonal then ((Real.exp Jright / R.eval x : ℝ) : ℂ) else 1) := by
  have hL := logCutoffPolynomialFactor_value L φ Jleft B D hB hD hφ hlip hout x
  have hR := logCutoffPolynomialFactor_value R φ Jright B D hB hD hφ hlip hout x
  have hone : onePolynomialFactor.value x = 1 := rfl
  have hrec := giantReciprocalFactor_cutoff R φ Jright B D hB hD hφ hlip hout x
  cases diagonal
  · simp only [giantOuterScalar, Bool.false_eq_true, ite_false, if_false, Complex.ofReal_one,
      giantOuterFactors, smoothPolynomialWeight, Fin.prod_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, one_mul, hL, hR, hone]
  · simp only [giantOuterScalar, ite_true, if_true, giantOuterFactors, smoothPolynomialWeight,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    calc
      _ = (logCutoffPolynomialFactor L φ Jleft B D hB hD hφ hlip).value x *
          ((logCutoffPolynomialFactor R φ Jright B D hB hD hφ hlip).value x *
            ((Real.exp 1 : ℂ) * (giantReciprocalFactor R Jright).value x)) := by ring
      _ = _ := by rw [hL, hrec]; ring

theorem giantOuterFactors_budget (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (diagonal : Bool) :
    smoothPolynomialBudget (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) =
      (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2) := by
  have hL := logCutoffPolynomialFactor_budget L φ Jleft B D hB hD hφ hlip
  have hR := logCutoffPolynomialFactor_budget R φ Jright B D hB hD hφ hlip
  cases diagonal
  · simp only [giantOuterFactors, Bool.false_eq_true, ite_false, if_false, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, onePolynomialFactor]
    rw [hL, hR]
    ring
  · simp only [giantOuterFactors, ite_true, if_true, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    rw [hL, hR, giantReciprocalFactor_budget]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-history kernel with its original outer priors and diagonal ratio -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem giantOuterWeight_polynomial (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    giantOuterWeight φ Jleft Jright diagonal (L.eval x) (R.eval x) =
      (giantOuterScalar diagonal : ℂ) *
        smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x :=
  (giantOuterFactors_value L R φ Jleft Jright B D hB hD hφ hlip hout diagonal x).symm

theorem giantOuterWeight_norm (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (L R : ℝ) :
    ‖giantOuterWeight φ Jleft Jright diagonal L R‖ ≤
      giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 *
        (if diagonal then 1 + Real.exp 2 else 2) := by
  have hs : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hv := giantOuterWeight_polynomial (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D
    hB hD hφ hlip hout diagonal 0
  simp only [Polynomial.eval_C] at hv
  rw [hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  have h := mul_le_mul_of_nonneg_left (smoothPolynomialWeight_norm
    (giantOuterFactors (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D hB hD hφ hlip diagonal) 0) hs
  rw [giantOuterFactors_budget] at h
  simpa only [mul_assoc] using h

theorem measurable_giantOuterWeight (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) :
    Measurable (fun z : ℝ × ℝ => giantOuterWeight φ Jleft Jright diagonal z.1 z.2) := by
  have hc (J : ℝ) : Measurable (fun x => (positiveLogCutoff φ J x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ J B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ J B D hB hD hφ hlip).continuous_value.congr he).measurable
  have hratio : Measurable (fun z : ℝ × ℝ => if diagonal then ((Real.exp Jright / z.2 : ℝ) : ℂ) else 1) := by
    cases diagonal
    · exact measurable_const
    · exact Complex.continuous_ofReal.measurable.comp (measurable_const.div measurable_snd)
  exact ((hc Jleft).comp measurable_fst |>.mul ((hc Jright).comp measurable_snd)).mul hratio

theorem measurable_movingOuterKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) :
    Measurable (fun z : ℝ × ℝ => movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal z.1 z.2) :=
  (measurable_movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout).mul
    (measurable_giantOuterWeight φ Jleft Jright B D hB hD hφ hlip hout diagonal)

theorem movingOuterKernel_slice_polynomial {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal coord : Bool) (fixed z : ℝ) :
    let W := fun b => movingSmoothPolynomialFactors value (T b)
      (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    let O := giantOuterFactors (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      φ Jleft Jright B D hB hD hφ hlip diagonal
    movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
      (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) =
      ((giantOuterScalar diagonal : ℂ) *
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed z) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed z)))) *
        smoothPolynomialWeight (Fin.append (pairedPolynomialFactors (W false) (W true)) O) z := by
  dsimp only
  unfold movingOuterKernel
  rw [movingRealKernelPair_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout]
  have hv := giantOuterWeight_polynomial (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
    φ Jleft Jright B D hB hD hφ hlip hout diagonal z
  rw [(movingCoordinate_eval coord fixed z).1, (movingCoordinate_eval coord fixed z).2] at hv
  rw [hv]
  simp only [smoothPolynomialWeight, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterSlices
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root and variation bounds with the original outer giant priors -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem smoothPolynomialBudget_append {n m : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (G : Fin m → ClippedPolynomialFactor) :
    smoothPolynomialBudget (Fin.append F G) = smoothPolynomialBudget F * smoothPolynomialBudget G := by
  unfold smoothPolynomialBudget
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem movingOuterPolynomialFactors_budget {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (diagonal : Bool) :
    smoothPolynomialBudget (movingOuterPolynomialFactors value T L R ψ X lo hi hlo hhi φ G
      Jleft Jright B D hB hD hφ hlip diagonal) ≤
      (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 *
        ((2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2)) := by
  have houter : 0 ≤ (2 * B + D * (Real.exp 2 - 1)) ^ 2 *
      (if diagonal then 1 + Real.exp 2 else 2) := by split <;> positivity
  rw [movingOuterPolynomialFactors, smoothPolynomialBudget_append, giantOuterFactors_budget]
  exact mul_le_mul_of_nonneg_right
    (movingPairedSmoothPolynomialFactors_budget value T L R ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip) houter

theorem giantOuterFactors_slice_no_roots (φ : ℝ → ℝ) (Jleft Jright B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (diagonal coord : Bool) (fixed : ℝ) (i : Fin 3) :
    ((giantOuterFactors (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      φ Jleft Jright B D hB hD hφ hlip diagonal i).polynomial.derivative).roots = 0 := by
  fin_cases i <;> cases coord <;> cases diagonal <;>
    simp [giantOuterFactors, movingCoordinateLeft, movingCoordinateRight,
      giantReciprocalFactor, reciprocalPolynomialFactor, logCutoffPolynomialFactor,
      Polynomial.derivative_mul, Polynomial.roots_C]

theorem movingOuterKernel_slice_roots {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (diagonal coord : Bool) (fixed : ℝ) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
    ∃ S : Finset ℝ, S.card + 1 ≤ 2 * movingKernelRootBudget n ∧
      (∀ i r, r ∈ (W i).polynomial.derivative.roots → r ∈ S) ∧
      (∀ x y, rootCellCode S x = rootCellCode S y →
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))) =
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed y) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed y)))) := by
  dsimp only
  obtain ⟨S, hS, hroots, hconst⟩ := movingRealKernelPair_slice_root_data value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  refine ⟨S, hS, ?_, hconst⟩
  intro i r
  refine Fin.addCases ?_ ?_ i
  · intro j hj
    apply hroots j r
    simpa only [movingOuterPolynomialFactors, Fin.append_left] using hj
  · intro j hj
    simp only [movingOuterPolynomialFactors, Fin.append_right,
      giantOuterFactors_slice_no_roots φ Jleft Jright B D hB hD hφ hlip diagonal coord fixed j,
      Multiset.notMem_zero] at hj

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterKernelRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime slice comparison with both outer priors and the diagonal ratio -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem PublishedProgressionInput.moving_outer_kernel_prime_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n)
      (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
      (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
      (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal coord : Bool) (fixed : ℝ)
      (Q q a : ℕ), 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 → ∀ c : ℂ,
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
        ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
      2 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexPrimeInterval q a u v (fun y => c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G
          Jleft Jright diagonal (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
        ∫ y in Set.Ioc u v, (c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
          (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤ Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.root_integral_prime_rate C d (2 * movingKernelRootBudget n)] with L hL
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal coord fixed Q q a hQ hq hqQ ha hlog u v hu huv hshort c
  dsimp only
  intro hbudget
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
    ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
  let gate := fun x => movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
    conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))
  let w := fun x => c * (giantOuterScalar diagonal : ℂ) * gate x
  have hscalar : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  obtain ⟨S, hS, hroots, hconst⟩ := movingOuterKernel_slice_roots value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal coord fixed
  have hw (x : ℝ) : ‖w x‖ ≤ ‖c‖ * giantOuterScalar diagonal := by
    have hg : ‖gate x‖ ≤ 1 := by
      dsimp only [gate]
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_mul (movingRealGateWeight_norm value (T false) (nodes false) X lo hi _)
        (movingRealGateWeight_norm value (T true) (nodes true) X lo hi _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    dsimp only [w]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hscalar]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) hscalar) hg
  have hc (x y : ℝ) (hcode : rootCellCode S x = rootCellCode S y) : w x = w y :=
    congrArg (c * (giantOuterScalar diagonal : ℂ) * ·) (hconst x y hcode)
  have he (z : ℝ) : w z * smoothPolynomialWeight W z =
      c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
        (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) := by
    rw [movingOuterKernel_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G
      Jleft Jright B D hB hD hφ hlip hout diagonal coord fixed z]
    dsimp only [w, W, gate, movingOuterPolynomialFactors]
    ring
  have h := hL Q q a hQ hq hqQ ha hlog u v hu huv hshort _ W S hS hroots w
    (‖c‖ * giantOuterScalar diagonal) (mul_nonneg (norm_nonneg _) hscalar) hw hc hbudget
  simpa only [he] using h

theorem moving_outer_kernel_integer_bound {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal coord : Bool) (fixed : ℝ)
    (q a : ℕ) (hq : 0 < q) (u v J : ℝ) (huv : u ≤ v) (c : ℂ) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
    ‖complexIntegerInterval q a u v J (fun y => c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G
        Jleft Jright diagonal (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
      ∫ y in Set.Ioc u v, (c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
        (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
        (integerLogDensity q J y : ℂ)‖ ≤
      4 * ((2 * movingKernelRootBudget n : ℕ) : ℝ) * (‖c‖ * giantOuterScalar diagonal) *
        smoothPolynomialBudget W * Real.exp (-J) := by
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
    ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
  let gate := fun x => movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
    conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))
  let w := fun x => c * (giantOuterScalar diagonal : ℂ) * gate x
  have hscalar : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  obtain ⟨S, hS, hroots, hconst⟩ := movingOuterKernel_slice_roots value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal coord fixed
  have hw (x : ℝ) : ‖w x‖ ≤ ‖c‖ * giantOuterScalar diagonal := by
    have hg : ‖gate x‖ ≤ 1 := by
      dsimp only [gate]
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_mul (movingRealGateWeight_norm value (T false) (nodes false) X lo hi _)
        (movingRealGateWeight_norm value (T true) (nodes true) X lo hi _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    dsimp only [w]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hscalar]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) hscalar) hg
  have hc (x y : ℝ) (hcode : rootCellCode S x = rootCellCode S y) : w x = w y :=
    congrArg (c * (giantOuterScalar diagonal : ℂ) * ·) (hconst x y hcode)
  have he (z : ℝ) : w z * smoothPolynomialWeight W z =
      c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
        (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) := by
    rw [movingOuterKernel_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G
      Jleft Jright B D hB hD hφ hlip hout diagonal coord fixed z]
    dsimp only [w, W, gate, movingOuterPolynomialFactors]
    ring
  have h := root_integral_integer_bound q a hq u v J huv W S hroots w
    (‖c‖ * giantOuterScalar diagonal) (mul_nonneg (norm_nonneg _) hscalar) hw hc
  simp only [he] at h
  apply h.trans
  have hK : ((S.card + 1 : ℕ) : ℝ) ≤ ((2 * movingKernelRootBudget n : ℕ) : ℝ) := by exact_mod_cast hS
  have hn : 0 ≤ 4 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W * Real.exp (-J) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) hscalar))
      (smoothPolynomialBudget_nonneg W)) (Real.exp_pos _).le
  calc
    _ = ((S.card + 1 : ℕ) : ℝ) *
        (4 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W * Real.exp (-J)) := by ring
    _ ≤ ((2 * movingKernelRootBudget n : ℕ) : ℝ) *
        (4 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W * Real.exp (-J)) :=
      mul_le_mul_of_nonneg_right hK hn
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterIntegerRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer slice rate with the original giant cutoff factors -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped Classical SchwartzMap

theorem moving_outer_kernel_integer_rate (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
      (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal coord : Bool) (fixed : ℝ)
      (q a : ℕ), 0 < q → ∀ u v J : ℝ, u ≤ v →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → ∀ c : ℂ,
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed)
        (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
      2 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexIntegerInterval q a u v J (fun y => c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
        ∫ y in Set.Ioc u v, (c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
          (integerLogDensity q J y : ℂ)‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [moving_pair_integer_error_rate n C d] with L hL
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal coord fixed q a hq u v J huv hJ c
  dsimp only
  intro hbudget
  apply (moving_outer_kernel_integer_bound value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi
    φ G Jleft Jright B D hB hD hφ hlip hout diagonal coord fixed q a hq u v J huv c).trans
  convert hL J _ hJ hbudget using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterJointComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint transport with the literal outer priors and diagonal reciprocal -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_outer_joint_mixed_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n)
      (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
      (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ),
      (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q a b : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q → b.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 → ∀ c : ℂ,
      2 * (‖c‖ * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
          c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y))) -
        ∫ x, ∫ y, c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
          ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) *
          (reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + Real.exp (v - J)) := by
  filter_upwards [P.moving_outer_kernel_prime_rate n C d, moving_outer_kernel_integer_rate n C d,
    eventually_ge_atTop (0 : ℝ)] with L hL hI hL0
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q a b hQ hq hqQ hb hlog u v r s J hJ huv hshort hr hrs hrshort c hbudget
  have hL := hL σ
  have hI := hI σ
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let H := fun x y => c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
  let μ := integerGiantMeasure q J u v
  let ν := primeGiantMeasure P Q q b r s
  let err := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L))
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  have : IsFiniteMeasure μ := finite_integerGiantMeasure q J u v
  have : IsFiniteMeasure ν := finite_primeGiantMeasure P Q q b r s (by linarith)
  have hscalar : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hsmall (coord : Bool) (fixed : ℝ) :
      2 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget
        (movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
          ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal) ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) :=
    (mul_le_mul_of_nonneg_left (movingOuterPolynomialFactors_budget value T _ _ ψ X lo hi V hlo hhi hV
      φ G Jleft Jright B D hB hD hφ hlip diagonal) (by positivity)).trans hbudget
  have hleft (y : ℝ) : ‖complexIntegerInterval q a u v J (fun x => H x y) - ∫ x, H x y ∂μ‖ ≤ err := by
    have h := hI value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
      diagonal false (Real.exp y) q a (by omega) u v J huv hJ c (hsmall false (Real.exp y))
    rw [integerGiantMeasure_integral q J u v]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, if_false, topGiantReal, ite_true, if_true] using h
  have hright (x : ℝ) : ‖complexPrimeInterval q b r s (H x) - ∫ y, H x y ∂ν‖ ≤ err := by
    have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
      diagonal true (Real.exp x) Q q b hQ hq hqQ hb hlog r s hr hrs hrshort c (hsmall true (Real.exp x))
    rw [primeGiantMeasure_integral P Q q b r s (by linarith)]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, if_false, topGiantReal, ite_true, if_true] using h
  have hmeas := measurable_exp_pair_mul
    (movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal)
    (measurable_movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal) c
  have hnorm (x y : ℝ) : ‖H x y‖ ≤ ‖c‖ *
      (((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 *
        (giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2))) := by
    dsimp only [H, movingOuterKernel]
    rw [norm_mul, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
    exact mul_le_mul (movingRealKernelPair_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _)
      (giantOuterWeight_norm φ Jleft Jright B D hB hD hφ hlip hout diagonal _ _) (norm_nonneg _) (by positivity)
  have hpair := mixed_pair_integral_transport q a b u v r s J μ ν H hmeas _ hnorm err err hleft hright
  have hmass : μ.real Set.univ ≤ Real.exp (v - J) :=
    integerGiantMeasure_mass_le q (by omega) J u v huv hshort
  apply hpair.trans
  have hmul := mul_le_mul_of_nonneg_left hmass (Real.exp_pos (-Real.exp ((125 / 10000 : ℝ) * L))).le
  dsimp only [err] at *
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ResidueIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue decompositions of the original giant sums -/

namespace Ostmann
open scoped BigOperators Classical

theorem reducedResidues_card_le (q : ℕ) : (reducedResidues q).card ≤ q := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range q)

theorem prime_mod_mem_reducedResidues (q p : ℕ) (hq : 0 < q) (hp : p.Prime) (hqp : q < p) :
    p % q ∈ reducedResidues q := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), ?_⟩
  have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hq hqp)
  rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec]
  exact hc.symm

theorem sum_residue_indicator (q : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a < q)
    (p : ℕ) (hp : p % q ∈ S) (z : ℂ) :
    (∑ a ∈ S, if Nat.ModEq q p a then z else 0) = z := by
  rw [Finset.sum_eq_single (p % q)]
  · simp only [Nat.ModEq, Nat.mod_mod, ite_true, if_true]
  · intro a ha hne
    have hnot : ¬ Nat.ModEq q p a := by
      intro h
      have he : p % q = a := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hS a ha)] using h
      exact hne he.symm
    simp only [hnot, ite_false, if_false]
  · exact fun hn => (hn hp).elim

theorem complexPrimeInterval_residues (q : ℕ) (hq : 0 < q) (u v : ℝ)
    (hlarge : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, p.Prime → q < p)
    (f : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v f =
      ∑ a ∈ reducedResidues q, complexPrimeInterval q a u v f := by
  unfold complexPrimeInterval
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · simp only [hprime, true_and, Nat.modEq_one, ite_true, if_true]
    exact (sum_residue_indicator q (reducedResidues q)
      (fun a ha => Finset.mem_range.mp (Finset.mem_filter.mp ha).1) p
      (prime_mod_mem_reducedResidues q p hq hprime (hlarge p hp hprime)) _).symm
  · simp only [hprime, false_and, ite_false, if_false, Finset.sum_const_zero]

theorem complexIntegerInterval_residues (q : ℕ) (hq : 0 < q) (u v J : ℝ) (f : ℝ → ℂ) :
    complexIntegerInterval 1 0 u v J f =
      ∑ a ∈ Finset.range q, complexIntegerInterval q a u v J f := by
  unfold complexIntegerInterval integerResidueAtom
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Nat.modEq_one, ite_true, if_true, apply_ite, Complex.ofReal_zero, mul_zero]
  exact (sum_residue_indicator q (Finset.range q) (fun a ha => Finset.mem_range.mp ha) p
    (Finset.mem_range.mpr (Nat.mod_lt _ hq)) _).symm

theorem complexPrimeInterval_finset_sum {A : Type*} (S : Finset A)
    (q a : ℕ) (u v : ℝ) (f : A → ℝ → ℂ) :
    complexPrimeInterval q a u v (fun y => ∑ i ∈ S, f i y) =
      ∑ i ∈ S, complexPrimeInterval q a u v (f i) := by
  unfold complexPrimeInterval
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp only [Finset.sum_mul, Finset.sum_const_zero]

theorem reciprocalPrimeInterval_le_exp (q a : ℕ) (u v : ℝ) :
    reciprocalPrimeInterval q a (Real.exp u) (Real.exp v) ≤ Real.exp (v - u) := by
  calc
    _ ≤ ∑ _p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, Real.exp (-u) := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · have hp0 : (0 : ℝ) < p := (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1)
        have hlog : Real.exp (-Real.log (p : ℝ)) = (p : ℝ)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log hp0]
        rw [← hlog]
        exact Real.exp_le_exp.mpr (neg_le_neg (log_mem_of_mem_exp_interval hp).1.le)
      · exact (Real.exp_pos _).le
    _ = ((⌊Real.exp v⌋₊ - ⌊Real.exp u⌋₊ : ℕ) : ℝ) * Real.exp (-u) := by simp
    _ ≤ Real.exp v * Real.exp (-u) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add, sub_eq_add_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimePairResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original two giant sums as a finite residue-pair sum -/

namespace Ostmann
open scoped BigOperators Classical

theorem finite_pair_comparison {A B : Type*} (S : Finset A) (T : Finset B)
    (F G : A → B → ℂ) (δ : ℝ) (h : ∀ a ∈ S, ∀ b ∈ T, ‖F a b - G a b‖ ≤ δ) :
    ‖(∑ a ∈ S, ∑ b ∈ T, F a b) - (∑ a ∈ S, ∑ b ∈ T, G a b)‖ ≤
      (S.card : ℝ) * T.card * δ := by
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ S, ‖∑ b ∈ T, (F a b - G a b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ S, ∑ b ∈ T, δ := by
      apply Finset.sum_le_sum
      intro a ha
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => h a ha b hb)
    _ = _ := by simp; ring

theorem mixed_pair_residue_factorization (q : ℕ) (hq : 0 < q) (u v r s J : ℝ)
    (hr : ∀ p ∈ Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊, p.Prime → q < p)
    (F : ℕ → ℕ → ℂ) (c : ℕ → ℕ → ℂ) (H : ℝ → ℝ → ℂ)
    (hfactor : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      ∀ t ∈ Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊, t.Prime →
      ∀ a ∈ Finset.range q, ∀ b ∈ reducedResidues q,
      Nat.ModEq q p a → Nat.ModEq q t b →
      F p t = c a b * H (Real.log p) (Real.log t)) :
    complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J
      (fun x => F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) =
      ∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
        complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J
          (fun x => c a b * H x y)) := by
  rw [complexPrimeInterval_residues q hq r s hr]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← complexPrimeInterval_finset_sum]
  apply complexPrimeInterval_congr
  intro t ht hprime htb
  have ht0 : (0 : ℝ) < t := by exact_mod_cast hprime.pos
  rw [Real.exp_log ht0, Nat.floor_natCast, complexIntegerInterval_residues q hq u v J]
  apply Finset.sum_congr rfl
  intro a ha
  apply complexIntegerInterval_congr
  intro p hp hpa
  have hp0 : (0 : ℝ) < p :=
    (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1)
  rw [Real.exp_log hp0, Nat.floor_natCast]
  exact hfactor p hp t ht hprime a ha b hb hpa htb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantResidueSumBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the number of giant residue pairs -/

namespace Ostmann
open Filter

theorem giant_residue_sum_error_rate (K : ℝ) (hK : 0 < K) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℕ, 0 < q →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      (q : ℝ) ^ 2 * K * Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) ≤
        Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  let C := |Real.log K| + 2
  filter_upwards [arithmetic_error_absorption (12 / 1000) (125 / 10000) (1225 / 100000)
    C 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hL hL1
  intro q hq hlog
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hfactor : (q : ℝ) ^ 2 * K ≤
      Real.exp (C * L ^ 0 + C * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    rw [← Real.exp_log (mul_pos (pow_pos hq0 2) hK), Real.exp_le_exp,
      Real.log_mul (pow_ne_zero 2 hq0.ne') hK.ne', Real.log_pow]
    have hC : 2 ≤ C := by dsimp [C]; linarith [abs_nonneg (Real.log K)]
    have hClog : Real.log K ≤ C := by dsimp [C]; linarith [le_abs_self (Real.log K)]
    have hLC : 2 ≤ C * L := le_trans hC (le_mul_of_one_le_right (by positivity : 0 ≤ C) hL1)
    have he := mul_le_mul_of_nonneg_right hLC (Real.exp_pos ((12 / 1000 : ℝ) * L)).le
    simp only [pow_zero, mul_one]
    linarith
  exact (mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le).trans
    (by simpa only [one_mul, neg_mul] using hL)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterResidueComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All residue pairs with both original outer giant priors -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_outer_mixed_residue_sum_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      (∀ a ∈ Finset.range q, ∀ b ∈ reducedResidues q,
      2 * (‖c a b‖ * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖(∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
          complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
            c a b * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)))) -
        (∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
          ∫ x, ∫ y, c a b * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
            ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v)‖ ≤
        Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_outer_joint_mixed_rate n C d,
    giant_residue_sum_error_rate (2 * Real.exp 1) (by positivity)] with L hL hR
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal V hV
    Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c hbudget
  have hL := hL σ
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let err := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L))
  have hm (b : ℕ) : reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) ≤ Real.exp 1 :=
    (reciprocalPrimeInterval_le_exp q b r s).trans (Real.exp_le_exp.mpr (by linarith))
  have hpoint (b : ℕ) (hb : b ∈ reducedResidues q) (a : ℕ) (ha : a ∈ Finset.range q) :
      ‖complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
          c a b * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y))) -
        ∫ x, ∫ y, c a b * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
          ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v‖ ≤ err * (2 * Real.exp 1) := by
    exact (hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal V hV
      Q q a b hQ hq hqQ (Finset.mem_filter.mp hb).2 hlog
      u v r s J hJ huv hshort hr hrs hrshort (c a b) (hbudget a ha b hb)).trans
      (mul_le_mul_of_nonneg_left (by
        have hmass : Real.exp (v - J) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
        linarith [hm b]) (Real.exp_pos _).le)
  apply (finite_pair_comparison (reducedResidues q) (Finset.range q) _ _ _ hpoint).trans
  have hc : ((reducedResidues q).card : ℝ) ≤ q := Nat.cast_le.mpr (reducedResidues_card_le q)
  calc
    _ ≤ (q : ℝ) * q * (err * (2 * Real.exp 1)) := by
      simp only [Finset.card_range]
      gcongr
    _ = (q : ℝ) ^ 2 * (2 * Real.exp 1) * err := by ring
    _ ≤ _ := hR q (by omega) hqlog

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_NaturalResidueAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural residue representatives and the Haar unit averages used by CRT -/

namespace Ostmann
open scoped BigOperators Classical

theorem sum_reducedResidues_eq_units (q : ℕ) [NeZero q] (f : ℕ → ℂ) :
    (∑ a ∈ reducedResidues q, f a) = ∑ a : (ZMod q)ˣ, f (a : ZMod q).val := by
  rw [← Finset.sum_coe_sort]
  exact ((unitReducedResidueEquiv q).sum_comp (fun a => f a.val)).symm

theorem sum_range_eq_zmod (q : ℕ) [NeZero q] (f : ℕ → ℂ) :
    (∑ a ∈ Finset.range q, f a) = ∑ a : ZMod q, f a.val := by
  rw [← Fin.sum_univ_eq_sum_range]
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GiantDensitySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving the finite residue average inside the common real integral -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

theorem double_integral_finset_sum {A : Type*} (S : Finset A)
    (μ ν : Measure ℝ) (F : A → ℝ → ℝ → ℂ)
    (hinner : ∀ a ∈ S, ∀ x, Integrable (F a x) ν)
    (houter : ∀ a ∈ S, Integrable (fun x => ∫ y, F a x y ∂ν) μ) :
    (∫ x, ∫ y, ∑ a ∈ S, F a x y ∂ν ∂μ) =
      ∑ a ∈ S, ∫ x, ∫ y, F a x y ∂ν ∂μ := by
  have hin (x : ℝ) : (∫ y, ∑ a ∈ S, F a x y ∂ν) =
      ∑ a ∈ S, ∫ y, F a x y ∂ν :=
    integral_finsetSum S (fun a ha => hinner a ha x)
  simp_rw [hin]
  exact integral_finsetSum S houter

/-- The complex residue coefficient is kept signed throughout this interchange. -/
theorem bounded_density_pair_sum {A B : Type*} (S : Finset A) (T : Finset B)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H))
    (K : ℝ) (hK : ∀ x y, ‖H x y‖ ≤ K)
    (α : A → ℝ → ℂ) (β : B → ℝ → ℂ)
    (hα : ∀ a ∈ S, Measurable (α a)) (hβ : ∀ b ∈ T, Measurable (β b))
    (U V : ℝ) (hU : 0 ≤ U) (_hV : 0 ≤ V)
    (hαU : ∀ a ∈ S, ∀ x, ‖α a x‖ ≤ U) (hβV : ∀ b ∈ T, ∀ x, ‖β b x‖ ≤ V)
    (c : A → B → ℂ) :
    (∑ a ∈ S, ∑ b ∈ T,
      ∫ x, ∫ y, c a b * H x y * α a x * β b y ∂ν ∂μ) =
      ∫ x, ∫ y, H x y * (∑ a ∈ S, ∑ b ∈ T, c a b * α a x * β b y) ∂ν ∂μ := by
  have hK0 : 0 ≤ K := (norm_nonneg (H 0 0)).trans (hK 0 0)
  let F := fun z : A × B => fun x y => c z.1 z.2 * H x y * α z.1 x * β z.2 y
  have hf (z : A × B) (hz : z ∈ S.product T) : Measurable (Function.uncurry (F z)) := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hz
    exact ((measurable_const.mul hH).mul ((hα z.1 ha).comp measurable_fst)).mul
      ((hβ z.2 hb).comp measurable_snd)
  have hn (z : A × B) (hz : z ∈ S.product T) (x y : ℝ) :
      ‖F z x y‖ ≤ ‖c z.1 z.2‖ * K * U * V := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hz
    dsimp only [F]
    simp only [norm_mul]
    apply mul_le_mul _ (hβV z.2 hb y) (norm_nonneg _) (mul_nonneg (by positivity) hU)
    apply mul_le_mul _ (hαU z.1 ha x) (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (hK x y) (norm_nonneg _)
  have hp (z : A × B) (hz : z ∈ S.product T) :
      Integrable (Function.uncurry (F z)) (μ.prod ν) :=
    ⟨(hf z hz).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun x => hn z hz x.1 x.2)⟩
  have hi (z : A × B) (hz : z ∈ S.product T) (x : ℝ) : Integrable (F z x) ν :=
    ⟨((hf z hz).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun y => hn z hz x y)⟩
  have hs := double_integral_finset_sum (S.product T) μ ν F hi (fun z hz => (hp z hz).integral_prod_left)
  simp only [Finset.product_eq_sprod, Finset.sum_product, F] at hs
  rw [← hs]
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RestrictedGiantDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded densities on the common real giant rectangle -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem measurable_restrictedPrimeGiantDensity (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) : Measurable (restrictedPrimeGiantDensity P Q q a u v) :=
  (Complex.continuous_ofReal.measurable.comp (measurable_selectedPrimeLogDensity P Q q a)).indicator
    measurableSet_Ioc

theorem restrictedPrimeGiantDensity_norm (P : PublishedProgressionInput) (Q q a : ℕ)
    (hq : 0 < q) (u v : ℝ) (hu : 1 ≤ u) (x : ℝ) :
    ‖restrictedPrimeGiantDensity P Q q a u v x‖ ≤ 2 := by
  by_cases hx : x ∈ Set.Ioc u v
  · simp only [restrictedPrimeGiantDensity, Set.indicator_of_mem hx,
      Complex.norm_real, Real.norm_eq_abs]
    exact primeLogDensity_abs_le_two _ _ _
      (by exact_mod_cast Nat.totient_pos.mpr hq) (pageCoefficient_abs_le_one _ _)
      (pageBeta_le_one _) (hu.trans hx.1.le)
  · simp only [restrictedPrimeGiantDensity, Set.indicator_of_notMem hx, norm_zero]
    norm_num

theorem primeGiantMeasure_restrict_integral (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 ≤ u) (f : ℝ → ℂ) :
    (∫ x, f x ∂primeGiantMeasure P Q q a u v) =
      ∫ x in Set.Ioc u v, f x * restrictedPrimeGiantDensity P Q q a u v x := by
  rw [primeGiantMeasure_integral P Q q a u v hu]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simp only [restrictedPrimeGiantDensity, Set.indicator_of_mem hx]

theorem measurable_restrictedIntegerGiantDensity (q : ℕ) (J u v : ℝ) :
    Measurable (restrictedIntegerGiantDensity q J u v) :=
  (Complex.continuous_ofReal.comp (continuous_integerLogDensity q J)).measurable.indicator
    measurableSet_Ioc

theorem restrictedIntegerGiantDensity_norm (q : ℕ) (hq : 0 < q) (J u v x : ℝ) :
    ‖restrictedIntegerGiantDensity q J u v x‖ ≤ Real.exp (v - J) := by
  by_cases hx : x ∈ Set.Ioc u v
  · simp only [restrictedIntegerGiantDensity, Set.indicator_of_mem hx,
      Complex.norm_real, Real.norm_eq_abs]
    exact integerLogDensity_abs_le q hq J hx.2
  · simp only [restrictedIntegerGiantDensity, Set.indicator_of_notMem hx, norm_zero]
    exact (Real.exp_pos _).le

theorem integerGiantMeasure_restrict_integral (q : ℕ) (J u v : ℝ) (f : ℝ → ℂ) :
    (∫ x, f x ∂integerGiantMeasure q J u v) =
      ∫ x in Set.Ioc u v, f x * restrictedIntegerGiantDensity q J u v x := by
  rw [integerGiantMeasure_integral q J u v]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simp only [restrictedIntegerGiantDensity, Set.indicator_of_mem hx]

theorem mixedGiantMeasure_pair_integral (P : PublishedProgressionInput) (Q q b : ℕ)
    (u v r s J : ℝ) (hr : 0 ≤ r) (H : ℝ → ℝ → ℂ) :
    (∫ x, ∫ y, H x y ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        H x y * restrictedIntegerGiantDensity q J u v x * restrictedPrimeGiantDensity P Q q b r s y := by
  rw [integerGiantMeasure_restrict_integral q J u v]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  dsimp only
  rw [primeGiantMeasure_restrict_integral P Q q b r s hr, ← integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y _
  ring

theorem mixedGiantMeasure_residue_integral (P : PublishedProgressionInput) (Q q : ℕ)
    (hq : 0 < q) (A B : Finset ℕ) (u v r s J : ℝ) (hr : 1 ≤ r)
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H)) (K : ℝ)
    (hK : ∀ x y, ‖H x y‖ ≤ K) (c : ℕ → ℕ → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B,
      ∫ x, ∫ y, c a b * H x y ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s, H x y *
        (∑ a ∈ A, ∑ b ∈ B, c a b * restrictedIntegerGiantDensity q J u v x *
          restrictedPrimeGiantDensity P Q q b r s y) := by
  simp_rw [mixedGiantMeasure_pair_integral P Q q _ u v r s J (by linarith)]
  exact bounded_density_pair_sum A B (volume.restrict (Set.Ioc u v)) (volume.restrict (Set.Ioc r s))
    H hH K hK (fun _ => restrictedIntegerGiantDensity q J u v)
    (fun b => restrictedPrimeGiantDensity P Q q b r s)
    (fun _ _ => measurable_restrictedIntegerGiantDensity q J u v)
    (fun b _ => measurable_restrictedPrimeGiantDensity P Q q b r s)
    (Real.exp (v - J)) 2 (by positivity) (by norm_num)
    (fun _ _ x => restrictedIntegerGiantDensity_norm q hq J u v x)
    (fun b _ x => restrictedPrimeGiantDensity_norm P Q q b hq r s hr x) c

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GiantHaarDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Haar residue factors inside the real giant integral -/

namespace Ostmann
open scoped BigOperators Classical

theorem selectedPrimeLogDensity_page (P : PublishedProgressionInput) (Q q a : ℕ) (x : ℝ) :
    (selectedPrimeLogDensity P Q q a x : ℂ) =
      pageGiantWeight P Q q a x / ((Nat.totient q : ℂ) * (x : ℂ)) := by
  simp only [selectedPrimeLogDensity, primeLogDensity, pageGiantWeight, pageMultiplier,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem mixed_pair_density_haar (P : PublishedProgressionInput) (Q q : ℕ) [NeZero q]
    (c : ℕ → ℕ → ℂ) (J x y : ℝ) :
    (∑ a ∈ Finset.range q, ∑ b ∈ reducedResidues q,
      c a b * (integerLogDensity q J x : ℂ) * (selectedPrimeLogDensity P Q q b y : ℂ)) =
      (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ) := by
  simp_rw [sum_range_eq_zmod, sum_reducedResidues_eq_units, selectedPrimeLogDensity_page]
  simp only [correctedMixedPairAverage, Fintype.card_prod, ZMod.card, ZMod.card_units_eq_totient,
    Nat.cast_mul, Fintype.sum_prod_type, integerLogDensity, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    div_eq_mul_inv, mul_inv_rev, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantHaarIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ideal giant main terms as a common real integral of Haar averages -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

theorem mixedGiantMeasure_pair_haar_integral (P : PublishedProgressionInput) (Q q : ℕ) [NeZero q]
    (u v r s J : ℝ) (hr : 1 ≤ r)
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H)) (K : ℝ)
    (hK : ∀ x y, ‖H x y‖ ≤ K) (c : ℕ → ℕ → ℂ) :
    (∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
      ∫ x, ∫ y, c a b * H x y ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        H x y * (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ) := by
  rw [Finset.sum_comm, mixedGiantMeasure_residue_integral P Q q (NeZero.pos q)
    (Finset.range q) (reducedResidues q) u v r s J hr H hH K hK c]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  simp only [restrictedIntegerGiantDensity, restrictedPrimeGiantDensity,
    Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  rw [mixed_pair_density_haar]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterHaarComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original outer-prior comparisons as corrected Haar integrals -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_outer_mixed_haar_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      (∀ a ∈ Finset.range q, ∀ b ∈ reducedResidues q,
      2 * (‖c a b‖ * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      letI : NeZero q := ⟨by omega⟩
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖(∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
          complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
            c a b * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_outer_mixed_residue_sum_rate n C d,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c hbudget
  have hL := hL σ
  have : NeZero q := ⟨by omega⟩
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let H := fun x y => movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
  have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D
    hB hD hφ hlip hout diagonal V hV Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c hbudget
  dsimp only at h ⊢
  have hmeas : Measurable (Function.uncurry H) := by
    have hh := measurable_exp_pair_mul
      (movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal)
      (measurable_movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal) (1 : ℂ)
    simpa only [one_mul] using hh
  have hnorm (x y : ℝ) : ‖H x y‖ ≤
      (((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 *
        (giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2))) := by
    dsimp only [H, movingOuterKernel]
    rw [norm_mul]
    exact mul_le_mul (movingRealKernelPair_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _)
      (giantOuterWeight_norm φ Jleft Jright B D hB hD hφ hlip hout diagonal _ _) (norm_nonneg _) (by positivity)
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  rw [mixedGiantMeasure_pair_haar_integral P Q q u v r s J hr1 H hmeas _ hnorm c] at h
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterNormBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform norm budget for the full giant kernel -/

namespace Ostmann
open scoped Classical ComplexConjugate SchwartzMap

theorem movingOuterKernel_norm_variation {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (L R : ℝ) :
    ‖movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal L R‖ ≤
      giantOuterScalar diagonal * movingOuterVariationBudget ψ V lo hi n B D diagonal := by
  have hs : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  let W := movingOuterPolynomialFactors value T (movingCoordinateLeft false R) (movingCoordinateRight false R)
    ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
  let g := movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair false R L) *
    conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair false R L))
  have hg : ‖g‖ ≤ 1 := by
    dsimp only [g]
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (movingRealGateWeight_norm value (T false) (nodes false) X lo hi _)
      (movingRealGateWeight_norm value (T true) (nodes true) X lo hi _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have he := movingOuterKernel_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G
    Jleft Jright B D hB hD hφ hlip hout diagonal false R L
  simp only [movingRealPair, Bool.false_eq_true, ite_false, if_false, topGiantReal, ite_true, if_true] at he
  have he' : movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal L R =
      ((giantOuterScalar diagonal : ℂ) * g) * smoothPolynomialWeight W L := he
  rw [he', norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  calc
    _ ≤ (giantOuterScalar diagonal * 1) * smoothPolynomialBudget W :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg hs) (smoothPolynomialWeight_norm W L)
        (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left
        (movingOuterPolynomialFactors_budget value T _ _ ψ X lo hi V hlo hhi hV φ G Jleft Jright B D hB hD hφ hlip diagonal) hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantCoprimeRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing only the top-giant coprimality test under the original laws -/

namespace Ostmann
open scoped BigOperators Classical

theorem weighted_coprime_removal_bound (P R : Finset ℕ) (ν μ : ℕ → ℝ)
    (hν : ∀ p ∈ P, 0 ≤ ν p) (hμ : ∀ r ∈ R, 0 ≤ μ r)
    (F : ℕ → ℕ → ℂ) (K : ℝ) (hF : ∀ p ∈ P, ∀ r ∈ R, ‖F p r‖ ≤ K) :
    ‖(∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * (if p.Coprime r then F p r else 0)) -
      ∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * F p r‖ ≤
      ∑ r ∈ R, μ r * (K * ∑ p ∈ P, if p.Coprime r then 0 else ν p) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ R, ‖(μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * (if p.Coprime r then F p r else 0) -
        (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * F p r‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ r hr)]
      apply mul_le_mul_of_nonneg_left _ (hμ r hr)
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
      by_cases hc : p.Coprime r
      · rw [ite_eq_left hc, ite_eq_left hc, sub_self, norm_zero, mul_zero]
      · simp only [hc, ite_false, if_false, mul_zero, zero_sub, norm_neg, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg (hν p hp)]
        exact (mul_le_mul_of_nonneg_left (hF p hp r hr) (hν p hp)).trans_eq (mul_comm _ _)

theorem integer_bad_coprime_mass (P : Finset ℕ) (ν : ℕ → ℝ)
    (N r : ℕ) (hr : r.Prime) (hpos : ∀ p ∈ P, 0 < p) (hN : ∀ p ∈ P, p ≤ N)
    (β : ℝ) (hβ : 0 ≤ β) (hmax : ∀ p ∈ P, ν p ≤ β) :
    (∑ p ∈ P, if p.Coprime r then 0 else ν p) ≤ β * (N / r : ℕ) := by
  have hs : P.filter (fun p => ¬ p.Coprime r) ⊆
      (Finset.range (N + 1)).filter (fun p => p ≠ 0 ∧ r ∣ p) := by
    intro p hp
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hN p hp; omega),
      Nat.ne_of_gt (hpos p hp), hr.dvd_iff_not_coprime.mpr (by simpa only [Nat.coprime_comm] using hc)⟩
  have hcard : (P.filter fun p => ¬ p.Coprime r).card ≤ N / r := by
    exact (Finset.card_le_card hs).trans_eq (Nat.card_multiples' N r)
  calc
    _ = ∑ p ∈ P.filter (fun p => ¬ p.Coprime r), ν p := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hc : p.Coprime r <;> simp [hc]
    _ ≤ ∑ _p ∈ P.filter (fun p => ¬ p.Coprime r), β :=
      Finset.sum_le_sum fun p hp => hmax p (Finset.mem_filter.mp hp).1
    _ = ((P.filter fun p => ¬ p.Coprime r).card : ℝ) * β := by simp
    _ ≤ (N / r : ℕ) * β := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hβ
    _ = _ := mul_comm _ _

theorem weighted_integer_prime_coprime_removal (P R : Finset ℕ) (ν μ : ℕ → ℝ)
    (N : ℕ) (hR : ∀ r ∈ R, r.Prime) (hpos : ∀ p ∈ P, 0 < p) (hN : ∀ p ∈ P, p ≤ N)
    (hν : ∀ p ∈ P, 0 ≤ ν p) (hμ : ∀ r ∈ R, 0 ≤ μ r)
    (β : ℝ) (hβ : 0 ≤ β) (hmax : ∀ p ∈ P, ν p ≤ β)
    (F : ℕ → ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ p ∈ P, ∀ r ∈ R, ‖F p r‖ ≤ K) :
    ‖(∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * (if p.Coprime r then F p r else 0)) -
      ∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * F p r‖ ≤
      K * β * N * ∑ r ∈ R, μ r / r := by
  refine (weighted_coprime_removal_bound P R ν μ hν hμ F K hF).trans ?_
  calc
    _ ≤ ∑ r ∈ R, μ r * (K * (β * ((N : ℝ) / r))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (hμ r hr)
      apply mul_le_mul_of_nonneg_left _ hK
      exact (integer_bad_coprime_mass P ν N r (hR r hr) hpos hN β hβ hmax).trans
        (mul_le_mul_of_nonneg_left Nat.cast_div_le hβ)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantCoprimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top coprimality error on the literal giant interval laws -/

namespace Ostmann
open scoped BigOperators Classical

theorem complexPrimeInterval_primeSum (u v : ℝ) (f : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v f =
      ∑ p ∈ giantPrimes u v, ((p : ℝ)⁻¹ : ℂ) * f (Real.log p) := by
  simp only [complexPrimeInterval, giantPrimes, Finset.sum_filter, Nat.modEq_one, and_true]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> simp only [hp, ite_true, if_true, ite_false, if_false, mul_comm]

theorem reciprocalPrimeInterval_primeSum (u v : ℝ) :
    reciprocalPrimeInterval 1 0 (Real.exp u) (Real.exp v) =
      ∑ p ∈ giantPrimes u v, (p : ℝ)⁻¹ := by
  simp only [reciprocalPrimeInterval, giantPrimes, Finset.sum_filter, Nat.modEq_one, and_true]

theorem mixed_pair_naturalSum (u v r s J : ℝ) (F : ℕ → ℕ → ℂ) :
    complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J
      (fun x => F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) =
      ∑ q ∈ giantPrimes r s, ((q : ℝ)⁻¹ : ℂ) *
        ∑ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, (Real.exp (-J) : ℂ) * F p q := by
  rw [complexPrimeInterval_primeSum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_filter.mp hq).2.pos
  rw [Real.exp_log hq0, Nat.floor_natCast]
  congr 1
  unfold complexIntegerInterval integerResidueAtom
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by
    have h := (Finset.mem_Ioc.mp hp).1
    have hpNat : 0 < p := Nat.zero_le _ |>.trans_lt h
    exact_mod_cast hpNat
  dsimp only
  rw [Real.exp_log hp0, Nat.floor_natCast]
  simp only [Nat.modEq_one, ite_true, if_true, mul_comm]

theorem mixed_pair_coprime_removal (u v r s J : ℝ) (F : ℕ → ℕ → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      ∀ q ∈ giantPrimes r s, ‖F p q‖ ≤ K) :
    ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
        if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ else 0)) -
      complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
        F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))‖ ≤
      K * Real.exp (v - J) * Real.exp (-r) *
        reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp s) := by
  rw [mixed_pair_naturalSum u v r s J (fun p q => if p.Coprime q then F p q else 0),
    mixed_pair_naturalSum u v r s J F, reciprocalPrimeInterval_primeSum]
  simp only [← Complex.ofReal_inv]
  refine (weighted_integer_prime_coprime_removal
    (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊) (giantPrimes r s)
    (fun _ => Real.exp (-J)) (fun q => (q : ℝ)⁻¹) ⌊Real.exp v⌋₊
    (fun _ hq => (Finset.mem_filter.mp hq).2)
    (fun p hp => Nat.zero_le _ |>.trans_lt (Finset.mem_Ioc.mp hp).1)
    (fun _ hp => (Finset.mem_Ioc.mp hp).2)
    (fun _ _ => (Real.exp_pos _).le) (fun _ _ => by positivity)
    _ (Real.exp_pos _).le (fun _ _ => le_rfl) F K hK hF).trans ?_
  have hsum : (∑ q ∈ giantPrimes r s, (q : ℝ)⁻¹ / q) ≤
      Real.exp (-r) * ∑ q ∈ giantPrimes r s, (q : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_filter.mp hq).2.pos
    have hi : (q : ℝ)⁻¹ ≤ Real.exp (-r) := by
      rw [← Real.exp_log hq0, ← Real.exp_neg]
      exact Real.exp_le_exp.mpr (neg_le_neg (log_mem_of_mem_exp_interval (Finset.mem_filter.mp hq).1).1.le)
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ (q : ℝ)⁻¹)
  have hN : (⌊Real.exp v⌋₊ : ℝ) ≤ Real.exp v := Nat.floor_le (Real.exp_pos _).le
  calc
    _ ≤ K * Real.exp (-J) * Real.exp v *
        (Real.exp (-r) * ∑ q ∈ giantPrimes r s, (q : ℝ)⁻¹) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hN (by positivity)) hsum
        (Finset.sum_nonneg fun q _ => by positivity) (by positivity)
    _ = _ := by rw [Real.exp_sub, Real.exp_neg]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantCoprimeRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top-giant coprimality loss is below the joint comparison error -/

namespace Ostmann
open Filter
open scoped Classical

theorem giant_coprime_error_rate (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ u K : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u →
      K ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      Real.exp 2 * (K * Real.exp (-u)) ≤ Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [weighted_giant_atom_rate C d,
    constant_mul_double_exp_le (Real.exp 2) 1 (13 / 1000) (125 / 10000)
      (Real.exp_pos _).le (by norm_num) (by norm_num) (by norm_num)] with L hL hconst
  intro u K hu hK
  exact (mul_le_mul_of_nonneg_left (hL u K hu hK) (Real.exp_pos _).le).trans
    (by simpa only [one_mul, neg_mul] using hconst)

theorem mixed_pair_coprime_removal_rate (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ u v r s J K : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → v ≤ J + 1 → s ≤ r + 1 → 0 ≤ K →
      K ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ∀ F : ℕ → ℕ → ℂ,
      (∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, ∀ q ∈ giantPrimes r s, ‖F p q‖ ≤ K) →
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
        if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ else 0)) -
        complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))‖ ≤ Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [giant_coprime_error_rate C d] with L hL
  intro u v r s J K hr hv hs hK hbudget F hF
  refine (mixed_pair_coprime_removal u v r s J F K hK hF).trans (le_trans ?_ (hL r K hr hbudget))
  have hm : reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp s) ≤ Real.exp (s - r) :=
    reciprocalPrimeInterval_le_exp 1 0 r s
  have he : Real.exp (v - J) * Real.exp (s - r) ≤ Real.exp 2 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ K * Real.exp (v - J) * Real.exp (-r) * Real.exp (s - r) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (K * Real.exp (-r)) * (Real.exp (v - J) * Real.exp (s - r)) := by ring
    _ ≤ (K * Real.exp (-r)) * Real.exp 2 := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := mul_comm _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantModulusCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant cells are above every prime factor of the common modulus -/

namespace Ostmann

theorem giant_interval_gt_modulus (L : ℝ) (hL : 0 < L) (M : ℕ) (hM : 0 < M)
    (hlog : Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L))
    (u v : ℝ) (hu : Real.exp ((49 / 1000 : ℝ) * L) ≤ u)
    (p : ℕ) (hp : p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊) : M < p := by
  have hgap : Real.exp ((12 / 1000 : ℝ) * L) < Real.exp ((49 / 1000 : ℝ) * L) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hlogp : Real.log (M : ℝ) < Real.log (p : ℝ) :=
    (hlog.trans_lt hgap).trans_le (hu.trans (log_mem_of_mem_exp_interval hp).1.le)
  have hp0 : (0 : ℝ) < p := (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have he := Real.exp_lt_exp.mpr hlogp
  rw [Real.exp_log hM0, Real.exp_log hp0] at he
  exact_mod_cast he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterCoprimeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coprime top giants under the literal prime and integer laws -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate_oai (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then
            c (⌊Real.exp x⌋₊ % q) (⌊Real.exp y⌋₊ % q) *
              movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊
          else 0)) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_outer_mixed_haar_rate n C d,
    mixed_pair_coprime_removal_rate C d, eventually_gt_atTop (0 : ℝ)] with L hL hR hL0
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c A hA0 hA hbudget
  have hL := hL σ
  have : NeZero q := ⟨by omega⟩
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let H := fun x y => movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
  let F0 := fun x y : ℕ => c (x % q) (y % q) *
    movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal x y
  let K := A * (giantOuterScalar diagonal * movingOuterVariationBudget ψ V lo hi n B D diagonal)
  have hs : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hv : 0 ≤ movingOuterVariationBudget ψ V lo hi n B D diagonal := by
    cases diagonal <;> unfold movingOuterVariationBudget <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true] <;> positivity
  have hK0 : 0 ≤ K := mul_nonneg hA0 (mul_nonneg hs hv)
  have hK : K ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    calc
      K ≤ 2 * K := by linarith
      _ = 2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal := by ring
      _ ≤ _ := hbudget
  have hnorm (x y : ℕ) : ‖F0 x y‖ ≤ K := by
    dsimp only [F0]
    rw [norm_mul]
    exact mul_le_mul (hA _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)))
      (movingOuterKernel_norm_variation value T nodes ψ X lo hi V hlo hhi hV φ G Jleft Jright B D
        hB hD hφ hlip hout diagonal x y) (norm_nonneg _) hA0
  have hremove := hR u v r s J K hr hvJ hrshort hK0 hK F0 (fun x _ y _ => hnorm x y)
  have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D
    hB hD hφ hlip hout diagonal V hV Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c (by
      intro a ha b hb
      have ha0 := Finset.mem_range.mp ha
      have hb0 := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hA a ha0 b hb0) hs) (by norm_num)) hv).trans hbudget)
  have hfactor := mixed_pair_residue_factorization q (by omega) u v r s J
    (fun z hz _ => giant_interval_gt_modulus L hL0 q (by omega) hqlog r s hr z hz)
    F0 c H (by
      intro x hx y _ hy a ha b hb hxa hyb
      have hx0 : (0 : ℝ) < x := (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hx).1)
      have hy0 : (0 : ℝ) < y := by exact_mod_cast hy.pos
      have ha0 : a < q := Finset.mem_range.mp ha
      have hb0 : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      have hxa' : x % q = a := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha0] using hxa
      have hyb' : y % q = b := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb0] using hyb
      dsimp only [F0, H]
      rw [hxa', hyb', Real.exp_log hx0, Real.exp_log hy0])
  dsimp only at h
  rw [← hfactor] at h
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hremove h)

end Ostmann

end OAI
end

theorem solution.{u} : type_of% @OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate_oai.{u} := @OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate_oai.{u}
