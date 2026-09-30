-- Prove2me | solution 1 for NumberField.Set.hasDirichletDensity_contraction
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:16:51.201012+00:00
-- url     : https://prove2.me/submissions/2eb56a58-d7e2-4f58-a0ed-b87d5ab66769

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_NumberField_DirichletDensityBounds
import Definitions.Def_TauCeti_NumberTheory_NumberField_ResidueDegree
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_encard_setOf_under_eq_le_finrank
import Theorems.Thm_NumberField_Set_HasDirichletDensity_of_symmDiff
import Theorems.Thm_NumberField_Set_hasDirichletDensity_iff_of_card_fiber_of_negligible
import Theorems.Thm_NumberField_Set_hasDirichletDensity_of_upperBound_of_lowerBound
import Theorems.Thm_Real_neg_log_one_sub_rpow_sub_le_div
import Theorems.Thm_Real_neg_log_one_sub_sub_le
import Theorems.Thm_TauCeti_LSeriesSummable_normCoeff_one_iff
import Theorems.Thm_TauCeti_card_filter_rationalPrimeBelow_le_finrank
import Theorems.Thm_TauCeti_dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub
import Theorems.Thm_TauCeti_sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum
import Theorems.Thm_TauCeti_summable_idealTerm_of_norm_normCoeff_eq_sum_norm
import Theorems.Thm_TauCeti_tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one
import Theorems.Thm_TauCeti_tsum_nat_rpow_neg_le_two

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Elementary bounds on real powers with a negative exponent

A base at least `2` raised to a negative exponent of size at least `1` is at most `1 / 2`. This
is the shape in which the local ratio of an Euler factor is bounded away from `1`, so that the
denominator `1 - y ^ (-s)` stays bounded below.

## Main results

* `Real.rpow_neg_le_half`: `y ^ (-s) ≤ 1 / 2` for `2 ≤ y` and `1 ≤ s`.
-/

 section

namespace Real

/-- If `2 ≤ y` and `1 ≤ s`, then `y ^ (-s) ≤ 1 / 2`. -/
theorem rpow_neg_le_half {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) : y ^ (-s) ≤ 1 / 2 :=
  calc y ^ (-s) ≤ (2 : ℝ) ^ (-s) := rpow_le_rpow_of_nonpos two_pos hy (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by norm_num

end Real

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Elementary bounds on `-log (1 - x)`

This file bounds the quadratic remainder `-log (1 - x) - x`, then specializes the estimate to
`x = y ^ (-s)`. The sharp factor `2` in the denominator comes from reading Mathlib's complex
logarithm bound along the reals. It also records the coarser estimate
`-log (1 - x) ≤ x + 2 x ^ 2` for `0 ≤ x ≤ 1/2`.

## Main results

* `Real.neg_log_one_sub_sub_le`: for `0 ≤ x < 1`, the remainder is at most
  `x² / (2 (1 - x))`.
* `Real.neg_log_one_sub_rpow_sub_le_div`: for `2 ≤ y` and `0 < s`, it is at most
  `y ^ (-2s) / (2 (1 - 2 ^ (-s)))`.
* `Real.neg_log_one_sub_rpow_sub_le`: for `2 ≤ y` and `1 ≤ s`, it is at most `y⁻²`.
* `Real.neg_log_one_sub_le_add_two_mul_sq`: for `0 ≤ x ≤ 1/2`, `-log (1 - x)` is at most
  `x + 2 x ^ 2`.
* `Complex.norm_neg_log_one_sub_sub_le`: for complex `z` with `‖z‖ ≤ 1/2`, the remainder
  `-log (1 - z) - z` has norm at most `‖z‖ ^ 2`.

## References

The shape of `Real.neg_log_one_sub_sub_le` follows the private declaration
`neg_log_one_sub_sub_le` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
C. Birkbeck and R. Brasca), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The sharper
constant here comes from Mathlib's `Complex.norm_log_one_sub_inv_sub_self_le`.
-/

 section

namespace Real

/-- The quadratic remainder of `-log (1 - x)` is nonnegative for `x < 1`. -/
theorem neg_log_one_sub_sub_nonneg {x : ℝ} (hx1 : x < 1) :
    0 ≤ -log (1 - x) - x := by
  linarith [log_le_sub_one_of_pos (sub_pos.mpr hx1)]



/-- For `1 < y` and `0 < s`, the quadratic remainder of `-log (1 - y ^ (-s))` is
nonnegative. -/
theorem neg_log_one_sub_rpow_sub_nonneg {y s : ℝ} (hy : 1 < y) (hs : 0 < s) :
    0 ≤ -log (1 - y ^ (-s)) - y ^ (-s) :=
  neg_log_one_sub_sub_nonneg (rpow_lt_one_of_one_lt_of_neg hy (by linarith))



/-- For `2 ≤ y` and `1 ≤ s`, the quadratic remainder of `-log (1 - y ^ (-s))` is at most
`y⁻²`. -/
theorem neg_log_one_sub_rpow_sub_le {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) :
    -log (1 - y ^ (-s)) - y ^ (-s) ≤ y ^ (-(2 : ℝ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hxhalf : y ^ (-s) ≤ 1 / 2 := rpow_neg_le_half hy hs
  calc
    -log (1 - y ^ (-s)) - y ^ (-s) ≤ (y ^ (-s)) ^ 2 / (2 * (1 - y ^ (-s))) :=
      neg_log_one_sub_sub_le (rpow_nonneg hy0.le _) (by linarith)
    _ ≤ (y ^ (-s)) ^ 2 := div_le_self (sq_nonneg _) (by linarith)
    _ = y ^ (-(2 * s)) := by rw [pow_two, ← rpow_add hy0, ← two_mul, mul_neg]
    _ ≤ y ^ (-(2 : ℝ)) := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- For `0 ≤ x ≤ 1/2`, `-log (1 - x) ≤ x + 2 x ^ 2`. -/
theorem neg_log_one_sub_le_add_two_mul_sq {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -log (1 - x) ≤ x + 2 * x ^ 2 := by
  -- The first-order Taylor estimate `|x + log (1 - x)| ≤ x ^ 2 / (1 - x)`.
  have h := abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one,
    abs_of_nonneg hx0] at h
  have h' : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  linarith [(abs_le.mp h).1]

end Real

namespace Complex



end Complex

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The divergence of `log (1 / (s - a))` as `s` decreases to `a`

`s ↦ log (1 / (s - a))` diverges to `+∞` on a right neighbourhood of `a`, for any real `a`. That
single limit is what this file provides.

The ratio statement it feeds is `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le`,
and lives there rather than here: once a denominator diverges, any numerator agreeing with it up
to a bounded additive error gives a quotient tending to `1`. A Dirichlet density argument uses
the case `a = 1`, with a prime sum estimated as `log (1 / (s - 1)) + O(1)` as the numerator, and
reads the density off the quotient — the divergence is exactly what makes the `O(1)` immaterial.
Nothing here is specific to that application, and the file contains no number theory.

## Main results

* `Real.tendsto_log_one_div_sub_atTop` — `log (1 / (s - a))` tends to `atTop` along `𝓝[>] a`.

## References

Adapted from `tendsto_log_one_div_sub_one_atTop` in
`CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The source states it at
`a = 1`; the statement here is at an arbitrary real translation point.
-/

 section

namespace Real

open Filter Topology

/-- `log (1 / (s - a))` tends to `+∞` as `s` decreases to `a`. At `a = 1` this is the divergence
driving the Dirichlet density asymptotics. -/
theorem tendsto_log_one_div_sub_atTop (a : ℝ) :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - a))) (𝓝[>] a) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - a) (𝓝[>] a) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right a).tendsto' a 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div, Pi.inv_def] using h1.inv_tendsto_nhdsGT_zero

end Real

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier; that value
is available from `ArithmeticFunction.map_zero`.

The construction is bundled as a complex-linear map.  The basic API exposes the finite norm fibre
`TauCeti.normFiber` and its finiteness, records the value at one, proves compatibility with
complex conjugation, and records in `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg` that no
cancellation occurs inside a fibre when the values of `f` are nonnegative.  Regrouping is
compatible with transporting along an isomorphism of number fields: `TauCeti.normCoeff_map` says
that an isomorphism `e : K ≃+* L` leaves every norm coefficient unchanged.

Regrouping loses information as soon as a norm fibre has more than one element:
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` produces a nonzero ideal arithmetic
function, with a negative value, whose norm coefficients all vanish.  This is the rejection test
that forbids weakening the nonnegativity hypothesis of the converse regrouping theorem to
nonnegativity of the coefficients themselves.

## Roadmap role

This is the finite-norm-fibre part of Layer **1.1** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The next layer step uses these coefficients
to regroup an absolutely convergent series over nonzero ideals into a Mathlib `LSeries`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]







/-- The absolute-norm fibre, viewed as a set, is the preimage of `{n}` under the absolute norm. -/
theorem coe_normFiber (n : ℕ) :
    (normFiber K n : Set ((Ideal (𝓞 K))⁰))
      = (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n} := by
  ext I
  simp







/-- The value of `normCoeff f` is the finite sum of `f` over the corresponding absolute-norm
fibre. -/
theorem normCoeff_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n =
      ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I :=
  (rfl)

/-- The value of `normCoeff f` as a sum over the finite absolute-norm fibre. -/
theorem normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := by
  rw [normCoeff_apply, finsum_mem_eq_finite_toFinset_sum _ (finite_normFiber K n)]
  simp only [normFiber]













/-- **Absence of cancellation inside norm fibres**, for a nonnegative ideal arithmetic function:
the absolute value of a norm coefficient is the sum of the absolute values over the fibre. -/
theorem norm_normCoeff_eq_sum_norm_of_nonneg (f : IdealArithmeticFunction K) (hf : ∀ I, 0 ≤ f I)
    (n : ℕ) : ‖normCoeff K f n‖ = ∑ I ∈ normFiber K n, ‖f I‖ := by
  have h : normCoeff K f n = ((∑ I ∈ normFiber K n, ‖f I‖ : ℝ) : ℂ) := by
    rw [normCoeff_eq_sum_normFiber]
    push_cast
    exact Finset.sum_congr rfl fun I _ ↦ Complex.eq_coe_norm_of_nonneg (hf I)
  rw [h, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]

/-! ### The cancellation rejection test -/



end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory`, `TauCeti.primeSummatory`, and `TauCeti.primePowerSummatory` the associated
summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

A prime-power ideal is `𝔭 ^ k` for a unique height-one prime `𝔭` and a unique `k ≥ 1`;
`TauCeti.primePowerBase` and `TauCeti.primePowerExponent` name that pair, and
`TauCeti.idealPrimePower_eq_of_base_eq_of_exponent_eq` records that it determines the ideal.  The
exponent is `1` exactly on the primes themselves, which is `TauCeti.primePowerExponent_eq_one_iff`;
`TauCeti.IdealPrimePower.ofPrime` is the resulting inclusion of the prime carrier into the
prime-power carrier, and `TauCeti.primePowerSummatory_eq_primeSummatory` uses it to read a
prime-power sum concentrated on the exponent-one part as a sum over primes.

`TauCeti.idealsLE_filter_dvd` identifies the ideals below a cutoff divisible by a fixed nonzero
ideal `P` with the multiples of `P`, and `TauCeti.idealSummatory_ite_dvd` reads the corresponding
part of a summatory function at the rescaled cutoff `x / N(P)`.

Two lemmas move a summatory function between the three carriers.
`TauCeti.idealSummatory_eq_primePowerSummatory` reads an ideal weight vanishing off the prime
powers as a prime-power weight, and `TauCeti.idealSummatory_eq_sum_range_normFiber` regroups an
ideal summatory function into the partial sum, over `n ≤ ⌊x⌋₊`, of the total mass on the norm
fibre at `n`; `TauCeti.idealSummatory_eq_sum_Icc_normCoeff` writes the same regrouping as a
partial sum of `TauCeti.normCoeff`.  Together they present a sum over prime powers as a partial
sum of an `ArithmeticFunction`, which is the shape a Tauberian theorem consumes.

For `0 ≤ x`, a real cutoff and its floor select the same indices, so
`TauCeti.normLE_eq_normLE_natFloor` and `TauCeti.summatory_eq_summatory_natFloor` convert between
the real and natural conventions. The small-cutoff cases are degenerate for a reason worth
recording: a nonzero ideal has absolute norm at least `1`, and a height-one prime at least `2`, so
`TauCeti.idealsLE_one` isolates the unit ideal and `TauCeti.primesLE_eq_empty_of_lt_two` empties the
prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density. In the same spirit,
`TauCeti.primeTheta_isLittleO_of_finite` records that a finite set of primes contributes an
eventually constant amount to `ϑ_K`, hence `o(x)`: an exceptional set can be discarded from a
counting argument outright, not merely from a density. Its `ψ` companion is
`TauCeti.primePsi_isLittleO_of_finite`.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite cutoff
carriers of 4.1, the generic summatory functions on ideals, primes, and prime powers of 4.2, and the
weighted prime counts `primeTheta` and `primeCount` of 4.3. Layer 5 supplies the actual size
estimates for these counts, and consumes the prime base and exponent of a prime-power ideal to
fibre those estimates over the primes.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/



variable (K : Type*) [Field K] [NumberField K]













variable {K}

/-- The absolute norm of a nonzero integral ideal is at least `1`, as a real number. -/
theorem one_le_absNorm_real_of_nonZeroDivisors (I : (Ideal (𝓞 K))⁰) :
    (1 : ℝ) ≤ Ideal.absNorm (I : Ideal (𝓞 K)) := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I





/-! ### The prime base and the exponent of a prime-power ideal -/



























































variable (K)

/-! ### Summatory functions over ideals and over primes -/

































variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)









/-! ### The weighted prime counts -/





variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

























































end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Regrouping an ideal-indexed Dirichlet series by absolute norm

An `TauCeti.IdealArithmeticFunction K` has two Dirichlet series attached to it: the series indexed
by the nonzero integral ideals of `𝓞 K`, whose terms are `TauCeti.idealTerm`, and the Mathlib
`LSeries` of the regrouped coefficients `TauCeti.normCoeff`. This file proves that the second is
obtained from the first by summing over the finite absolute-norm fibres, so that absolute
convergence of the ideal-indexed series transfers to the `LSeries` together with the value of the
sum.

## Main definitions

* `TauCeti.idealTerm f s I` is the term `f I / N(I) ^ s` of the ideal-indexed Dirichlet series.
* `TauCeti.idealAbscissaOfAbsConv f` is the abscissa of absolute convergence of that series, the
  ideal-indexed analogue of Mathlib's `LSeries.abscissaOfAbsConv`.

## Main results

* `TauCeti.regroupByNorm`: if the ideal-indexed series has sum `L` at `s`, then so does the
  `LSeries` of `TauCeti.normCoeff f`; `TauCeti.LSeriesSummable_normCoeff` and
  `TauCeti.LSeries_normCoeff` are the summability and value statements it packages.
* `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`: weighting the ideal terms
  by `log N(I)` keeps them summable strictly to the right of a point of absolute convergence.
* `TauCeti.abscissaOfAbsConv_normCoeff_le`: consequently the grouped abscissa of absolute
  convergence is at most the ideal-indexed one.
* `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm`: the converse holds whenever no
  cancellation occurs inside a norm fibre. `TauCeti.summable_idealTerm_of_nonneg` and
  `TauCeti.idealAbscissaOfAbsConv_eq_abscissaOfAbsConv` specialize it to the case where every
  *individual ideal summand* is nonnegative, where moreover the two abscissae agree.

## Implementation notes

The regrouping is an instance of Mathlib's `HasSum.tsum_fiberwise` along the absolute norm
`fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K))`, whose fibres are the finite sets
`TauCeti.normFiber K n`. Absolute convergence of the ideal-indexed series is expressed as plain
`Summable`, which for a complex-valued family is unconditional convergence and hence absolute
convergence; no rearrangement hypothesis is therefore needed for the transfer.

The converse is proved through `summable_partition` applied to the norms of the terms. All it
needs about `f` is that the norm of each grouped coefficient is the sum of the norms over its
fibre — the absence of cancellation inside the fibre. Nonnegativity of every ideal summand is one
way to secure that, through `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg`; it is the step that
fails under cancellation, as the rejection test
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` records. That test is a statement about
`TauCeti.normCoeff` alone, so it lives with that definition rather than here.

## Roadmap role

This is Layer **1.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`; the required worked
example 9 accompanies it in `TauCeti/NumberTheory/ArithmeticDirichletSeries/NormCoeff.lean`. The
exact value of the abscissa for the trivial weight is deliberately not proved here: its divergence
input is the Layer 5 ideal count of
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Estimates.lean`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### The ideal-indexed term -/



/-- Defining equation of `TauCeti.idealTerm`. -/
theorem idealTerm_def (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f s I = f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s :=
  (rfl)

/-- The absolute value of an ideal term depends on `s` only through its real part. -/
@[simp]
theorem norm_idealTerm (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f s I‖ = ‖f I‖ / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re := by
  rw [idealTerm_def, norm_div,
    Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors I)]









/-! ### Regrouping -/

/-- The `n`-th term of the regrouped `LSeries` is the finite sum of the ideal terms over the
absolute-norm fibre of `n`. -/
theorem term_normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (s : ℂ) (n : ℕ) :
    LSeries.term (normCoeff K f) s n = ∑ I ∈ normFiber K n, idealTerm K f s I := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, normCoeff_eq_sum_normFiber, Finset.sum_div]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  rw [idealTerm_def, (mem_normFiber K).mp hI]

/-- The regrouped `LSeries` terms as the fibrewise sums of the ideal terms along the absolute
norm. This is the form consumed by `HasSum.tsum_fiberwise`; `term_normCoeff_eq_sum_normFiber` is
the usable finite-fibre formula. -/
private theorem term_normCoeff (f : IdealArithmeticFunction K) (s : ℂ) :
    LSeries.term (normCoeff K f) s = fun n ↦
      ∑' I : (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
        idealTerm K f s I := by
  funext n
  rw [← coe_normFiber, Finset.tsum_subtype' (normFiber K n) (idealTerm K f s)]
  exact term_normCoeff_eq_sum_normFiber K f s n

/-- **Regrouping by absolute norm.** If the Dirichlet series indexed by the nonzero integral ideals
converges absolutely at `s` with sum `L`, then the Mathlib `LSeries` of the regrouped coefficients
`TauCeti.normCoeff f` converges absolutely at `s` with the same sum.

Absolute convergence of the ideal-indexed series is the hypothesis `HasSum`, which for a
complex-valued family is unconditional. No hypothesis on the individual ideal summands is needed;
compare `TauCeti.summable_idealTerm_of_nonneg` for the converse, which does need one. -/
theorem regroupByNorm {f : IdealArithmeticFunction K} {s L : ℂ} (h : HasSum (idealTerm K f s) L) :
    LSeriesHasSum (normCoeff K f) s L := by
  simpa only [LSeriesHasSum, term_normCoeff] using
    h.tsum_fiberwise fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))

/-- Absolute convergence of the ideal-indexed Dirichlet series implies that of the regrouped
`LSeries`. -/
theorem LSeriesSummable_normCoeff {f : IdealArithmeticFunction K} {s : ℂ}
    (h : Summable (idealTerm K f s)) : LSeriesSummable (normCoeff K f) s :=
  LSeriesHasSum.LSeriesSummable (regroupByNorm K h.hasSum)



/-! ### The ideal-indexed abscissa of absolute convergence -/













/-! ### The converse, in the absence of cancellation inside norm fibres -/







/-- **The converse regrouping, under nonnegativity of every ideal summand.** If every value of `f`
is a nonnegative real number, then absolute convergence of the regrouped `LSeries` implies absolute
convergence of the ideal-indexed series.

This is the special case of `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm` in which
nonnegativity rules out cancellation. Nonnegativity of the *grouped* coefficients
`TauCeti.normCoeff f` does not suffice; see
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg`. -/
theorem summable_idealTerm_of_nonneg (f : IdealArithmeticFunction K) (hf : ∀ I, 0 ≤ f I) {s : ℂ}
    (h : LSeriesSummable (normCoeff K f) s) : Summable (idealTerm K f s) :=
  summable_idealTerm_of_norm_normCoeff_eq_sum_norm K f
    (norm_normCoeff_eq_sum_norm_of_nonneg K f hf) h



end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Linear ideal counts and the exact abscissa of the trivial ideal weight

Mathlib's `NumberField.Ideal.tendsto_norm_le_div_atTop₀` says that the number of nonzero integral
ideals of `𝓞 K` of absolute norm at most `x` is asymptotic to `ρ x`, with `ρ` the positive residue
of the Dedekind zeta function.  This file turns that single asymptotic into the *two-sided* linear
bounds that every later estimate of the roadmap counts against, and then spends them on the exact
abscissa of absolute convergence of the trivial ideal weight.

Both directions are needed.  Convergence uses the upper bound alone: it makes the partial sums of
the norm coefficients `O(n)`, so Mathlib's `LSeriesSummable_of_sum_norm_bigO` gives absolute
convergence on `Re s > 1`.  Divergence at `s = 1` uses both bounds together, to estimate the mass
of a block `N < n ≤ m N` of fixed ratio `m` as a difference of endpoint counts: the lower bound at
the right endpoint `m N` and the upper bound at the left endpoint `N` leave the block at least
`lower * m N - upper * N` of coefficient mass, so the terms `‖a n‖ / n` add up to at least
`lower - upper / m`, which is at least `lower / 2` once `m ≥ 2 * upper / lower`, while the blocks
of a convergent series of nonnegative terms must become arbitrarily small.

## Main definitions

* `TauCeti.IdealCountingLinearBounds K` packages positive constants `lower` and `upper` with the
  two-sided bound `lower * x ≤ #{I ≠ 0 | N(I) ≤ x} ≤ upper * x`, valid from cutoff `1` on.
* `TauCeti.card_primePowersLE_isBigO` transfers the upper ideal-count bound to the number of
  prime-power ideals at most `x`.

## Main results

* `TauCeti.idealCount_linearBounds`: such a package exists for every number field.
* `TauCeti.abscissaOfAbsConv_normCoeff_one`: the abscissa of absolute convergence of the trivial
  ideal weight is exactly `1`; `TauCeti.LSeriesSummable_normCoeff_one_iff` is the sharp
  convergence criterion.
* `TauCeti.abscissaOfAbsConv_dedekindZetaCoeff` and `TauCeti.LSeriesSummable_dedekindZetaCoeff_iff`
  are the same two statements for `TauCeti.dedekindZetaCoeff`, the coefficient system Mathlib's
  `NumberField.dedekindZeta` is the `LSeries` of.  That system counts *all* integral ideals, so it
  differs from the trivial norm coefficients at `n = 0` and the two statements are related only
  through the `n ≠ 0` congruence `LSeries.abscissaOfAbsConv_congr`.
* `TauCeti.summable_idealTerm_of_bounded_of_one_lt_re`: a uniformly bounded weight has an
  absolutely convergent ideal-indexed Dirichlet series on `Re s > 1`, and
  `TauCeti.summable_idealTerm_of_unitary_of_one_lt_re` is its unitary specialization.
* `TauCeti.idealAbscissaOfAbsConv_lt_re_of_bounded`: the same hypothesis places the ideal-indexed
  abscissa of absolute convergence strictly below every `Re s > 1`.

## Implementation notes

The counting function is Mathlib's own
`Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}`, written out rather
than abbreviated, so that the bounds apply to `NumberField.Ideal.tendsto_norm_le_div_atTop₀`
without a translation lemma.  The inclusive real cutoff is the one fixed by the conventions table
of the roadmap.

`TauCeti.NumberTheory.EffectiveBounds.IdealCount` proves the *effective* bound
`#{I ≠ 0 | N(I) ≤ x} ≤ x² 2^[K:ℚ]`, with an explicit constant but the wrong exponent; it cannot
prove convergence at `Re s > 1`, and it has no lower bound at all.

## Relationship to other estimates

The unweighted prime-power cardinality estimate is separate from the weighted higher-prime-power
estimates in `HigherPrimePowers.lean`.  The abscissa results above depend only on the two-sided
linear ideal counts, not on the analytic continuation of the Dedekind zeta function or its pole at
`s = 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField _root_.Topology _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### Finiteness and monotonicity of the ideal count -/







/-! ### Two-sided linear bounds -/











/-! ### Partial sums of the trivial norm coefficients -/







/-! ### The exact abscissa of the trivial ideal weight -/















/-! ### The exact abscissa, and its Dedekind zeta form -/





/-- The ideal-indexed Dirichlet series of the trivial ideal weight converges absolutely exactly on
`Re s > 1`. -/
theorem summable_idealTerm_one_iff {K : Type*} [Field K] [NumberField K] {s : ℂ} :
    Summable (idealTerm K (1 : IdealArithmeticFunction K) s) ↔ 1 < s.re := by
  refine ⟨fun h ↦ (LSeriesSummable_normCoeff_one_iff K).mp (LSeriesSummable_normCoeff K h),
    fun h ↦ ?_⟩
  exact summable_idealTerm_of_nonneg K 1 (fun _ ↦ zero_le_one)
    ((LSeriesSummable_normCoeff_one_iff K).mpr h)











end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Convergence of the ideal- and prime-indexed Dirichlet series

The nonzero integral ideals of `𝓞 K` carry the Dirichlet series `∑ N(I) ^ (-s)`, whose abscissa
of absolute convergence is exactly `1`: that is `TauCeti.summable_idealTerm_one_iff`, read off
from the two-sided linear ideal counts.  Distinct height-one primes are distinct nonzero
integral ideals, so the prime-indexed series `∑ N(𝔭) ^ (-s)` is a subfamily of that one, and
converges for every `s > 1`.  Only convergence transfers this way, not the abscissa: divergence
of the all-prime sum at `s = 1` is a separate statement, and is not proved here.

`NumberField.Set.primeIdealZetaSum S s` is that sum restricted to a set `S` of primes.  It is a
`tsum`, and a `tsum` takes the junk value `0` on a family that is not summable, so summability
is what separates a statement about the prime Dirichlet sum from a statement about that junk
value.  The results below supply it for every `s > 1` and every set of primes.

## Main results

* `TauCeti.summable_absNorm_rpow_ideal_iff`: over the nonzero integral ideals of `𝓞 K`, the
  series `∑ N(I) ^ (-s)` converges exactly for `1 < s`.  This is the real-variable form of
  `TauCeti.summable_idealTerm_one_iff`.
* `TauCeti.summable_absNorm_rpow_primes_of_one_lt`: over the height-one primes of `𝓞 K`, the
  series `∑ N(𝔭) ^ (-s)` converges for every `1 < s`.
* `TauCeti.summable_absNorm_rpow_subtype_of_one_lt`: the same over an arbitrary set of
  height-one primes.  This is the family `NumberField.Set.primeIdealZetaSum` sums, so it is the
  form its consumers need.
* `NumberField.Set.primeIdealZetaSum_univ`: the prime ideal zeta sum over all height-one primes as
  a sum over the whole height-one spectrum.
* `NumberField.Set.primeIdealZetaSum_mono_set`: the prime ideal zeta sum is monotone under
  inclusion of sets of primes, given summability over the larger set;
  `NumberField.Set.primeIdealZetaSum_mono_set_of_one_lt` is its `1 < s` specialization.
* `NumberField.Set.primeIdealZetaSum_pos`: a summable sum over a nonempty set of primes is
  positive; `NumberField.Set.primeIdealZetaSum_univ_pos` applies this to all primes. The
  corresponding `_of_one_lt` lemmas supply summability from `1 < s`.

## Implementation notes

The prime-indexed statement is obtained by restricting the ideal-indexed one along
`𝔭 ↦ 𝔭.asIdeal`, which is injective into `(Ideal (𝓞 K))⁰`, rather than by comparing each
`N(𝔭) = p ^ f` with the rational prime `p` below it and summing over the rational primes.  The
restriction is the shorter route on the full set of primes, and reuses the exact abscissa already
established for the trivial ideal weight.  The comparison route is not redundant: on the primes
of residue degree above one it yields the strictly wider half-line `s > 1/2`, and
`TauCeti.summable_absNorm_rpow_higherDegreePrimes` takes it for exactly that reason.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* Adapted from the Birkbeck–Brasca Chebotarev density project,
  <https://github.com/CBirkbeck/chebotarev-density> (Apache-2.0), commit
  `8575c9df1ae0a61120ab5c964c7911414254bec7`, file `CebotarevDensity/Density.lean`:
  `summable_absNorm_rpow_ideal_iff` from `summable_nonzeroIdeal_absNorm_rpow`,
  `summable_absNorm_rpow_subtype_of_one_lt` from `summable_prime_absNorm_rpow`, and
  `NumberField.Set.primeIdealZetaSum_mono_set` from `primeIdealZetaSum_le_of_subset`.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti


/-! ### The ideal-indexed series, as a real Dirichlet series -/

/-- **The ideal-indexed Dirichlet series converges exactly on `s > 1`.** The real-variable form
of `TauCeti.summable_idealTerm_one_iff`, stated for the real power `N(I) ^ (-s)` rather than for
the complex term `TauCeti.idealTerm`, which is the shape the prime-indexed results below meet. -/
@[simp]
theorem summable_absNorm_rpow_ideal_iff {s : ℝ} :
    (Summable fun I : (Ideal (𝓞 K))⁰ ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)) ↔ 1 < s := by
  -- Each real term is the norm of the complex term at `s`, and norms decide summability.
  have key : (fun I : (Ideal (𝓞 K))⁰ ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s))
      = fun I ↦ ‖idealTerm K (1 : IdealArithmeticFunction K) (s : ℂ) I‖ :=
    funext fun I ↦ by simp [Real.rpow_neg]
  rw [key, summable_norm_iff, summable_idealTerm_one_iff, Complex.ofReal_re]

/-! ### The prime-indexed series -/

/-- **The prime-indexed Dirichlet series converges for `s > 1`.** The height-one-prime analogue of
`TauCeti.summable_absNorm_rpow_ideal_iff`. -/
theorem summable_absNorm_rpow_primes_of_one_lt {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  -- Every height-one prime is a nonzero integral ideal and is determined by that ideal, so the
  -- prime-indexed family is an injective reindexing of a subfamily of the ideal-indexed one.
  -- The injectivity is Mathlib's `HeightOneSpectrum.asIdeal_injective` factored through the
  -- `nonZeroDivisors` coercion; nothing about it is proved here.
  have hinj : Function.Injective fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ : (Ideal (𝓞 K))⁰) :=
    Function.Injective.of_comp (f := Subtype.val) HeightOneSpectrum.asIdeal_injective
  exact ((summable_absNorm_rpow_ideal_iff.mpr hs).comp_injective hinj).congr fun _ ↦ rfl

/-- **Restricted to any set of height-one primes**, the prime-indexed Dirichlet series still
converges for `s > 1`: a subfamily of a summable family is summable.

This is the family `NumberField.Set.primeIdealZetaSum` sums, so it is the summability its
consumers need in order to denote a genuine sum rather than the `tsum` junk value. -/
theorem summable_absNorm_rpow_subtype_of_one_lt (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ}
    (hs : 1 < s) : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) :=
  (summable_absNorm_rpow_primes_of_one_lt hs).subtype S

end TauCeti

namespace NumberField.Set

open _root_.TauCeti

/-- The prime ideal zeta sum over all height-one primes is the sum over the whole height-one
spectrum. -/
@[simp]
theorem primeIdealZetaSum_univ (s : ℝ) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
      ∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
  rw [primeIdealZetaSum_def,
    tsum_univ fun P : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)]

/-- **The prime ideal zeta sum is monotone under inclusion of sets of primes.** The hypothesis is
summability over the larger set, which is what the proof actually consumes: a sparse set of primes
can be summable well outside the half-line on which the all-prime series converges.
`primeIdealZetaSum_mono_set_of_one_lt` is the specialization to `1 < s`.

Summability is not decoration: `tsum` returns `0` on a family that is not summable, so an
inequality between two such sums can fail with a positive left-hand side and a vanishing right. -/
theorem primeIdealZetaSum_mono_set {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T) {s : ℝ}
    (hT : Summable fun 𝔭 : T ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    S.primeIdealZetaSum s ≤ T.primeIdealZetaSum s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  -- Enlarging the set of primes adds nonnegative terms to a convergent sum: `Set.inclusion hST`
  -- is injective, and matches the terms of the two sums exactly; summability over `S` is the
  -- restriction of `hT` along that inclusion.
  exact (hT.comp_injective (Set.inclusion_injective hST)).tsum_le_tsum_of_inj (Set.inclusion hST)
    (Set.inclusion_injective hST) (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl) hT

/-- The `1 < s` specialization of `primeIdealZetaSum_mono_set`, where summability over the larger
set is automatic. -/
theorem primeIdealZetaSum_mono_set_of_one_lt {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T)
    {s : ℝ} (hs : 1 < s) : S.primeIdealZetaSum s ≤ T.primeIdealZetaSum s :=
  primeIdealZetaSum_mono_set hST (summable_absNorm_rpow_subtype_of_one_lt T hs)









end NumberField.Set

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# One-sided bounds for Dirichlet density

For a set `S` of nonzero prime ideals of a number field, Mathlib's
`NumberField.Set.HasDirichletDensity S δ` says that the ratio

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s`

tends to `δ` as `s` approaches `1` from the right.  Squeeze arguments often produce the two
sides of this limit separately.  This file records those one-sided conclusions as
`NumberField.Set.IsLowerDirichletDensityBound S δ` and
`NumberField.Set.IsUpperDirichletDensityBound S δ`.

The predicates use eventual epsilon inequalities, rather than assigning junk-valued lower and
upper densities.  They are monotone in the proposed bound, and a common lower and upper bound
forces a Dirichlet density.  A lower bound is always at most an upper bound; this
comparison also gives the natural interval restrictions on one-sided bounds.

## Main results

* `NumberField.Set.hasDirichletDensity_iff`: Mathlib's `HasDirichletDensity`, unfolded to the
  convergence of the defining ratio.
* `NumberField.Set.HasDirichletDensity.isLowerDirichletDensityBound` and
  `NumberField.Set.HasDirichletDensity.isUpperDirichletDensityBound`: a Dirichlet density is
  both a lower and an upper bound.
* `NumberField.Set.isLowerDirichletDensityBound_of_forall_lt` and
  `NumberField.Set.isUpperDirichletDensityBound_of_forall_gt`: a value is a lower (upper) bound as
  soon as every smaller (larger) value is.
* `NumberField.Set.IsLowerDirichletDensityBound.le_of_isUpperDirichletDensityBound`:
  every lower bound is at most every upper bound.
* `NumberField.Set.hasDirichletDensity_of_upperBound_of_lowerBound`: matching one-sided bounds
  force a Dirichlet density.
* `NumberField.Set.hasDirichletDensity_iff_bounds`: the resulting characterization of
  Dirichlet density.

## References

* J.-P. Serre, *Corps locaux*, Chapter VI.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.Topology

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]

/-- Unfolds `HasDirichletDensity S δ` to the convergence, as `s → 1⁺`, of the ratio of the
partial prime sum over `S` to the sum over all primes. -/
theorem hasDirichletDensity_iff {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    S.HasDirichletDensity δ ↔
      Tendsto (fun s : ℝ ↦ S.primeIdealZetaSum s /
        NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s)
        (𝓝[>] 1) (𝓝 δ) :=
  Iff.rfl





/-- Characteristic restatement of a lower Dirichlet-density bound. -/
theorem isLowerDirichletDensityBound_iff
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    IsLowerDirichletDensityBound S δ ↔
      ∀ ε, 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 1,
        δ - ε < S.primeIdealZetaSum s /
          NumberField.Set.primeIdealZetaSum
            (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s :=
  Iff.rfl

/-- Characteristic restatement of an upper Dirichlet-density bound. -/
theorem isUpperDirichletDensityBound_iff
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    IsUpperDirichletDensityBound S δ ↔
      ∀ ε, 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 1,
        S.primeIdealZetaSum s /
          NumberField.Set.primeIdealZetaSum
            (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s < δ + ε :=
  Iff.rfl



-- The proof below follows `NumberField.Set.HasDirichletDensity.le_one` from
-- `Mathlib.NumberTheory.NumberField.DirichletDensity`.














/-- A Dirichlet density is a lower Dirichlet-density bound. -/
theorem HasDirichletDensity.isLowerDirichletDensityBound
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} (h : S.HasDirichletDensity δ) :
    IsLowerDirichletDensityBound S δ := by
  intro ε hε
  exact (tendsto_order.1 (hasDirichletDensity_iff.1 h)).1 (δ - ε) (by linarith)

/-- A Dirichlet density is an upper Dirichlet-density bound. -/
theorem HasDirichletDensity.isUpperDirichletDensityBound
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} (h : S.HasDirichletDensity δ) :
    IsUpperDirichletDensityBound S δ := by
  intro ε hε
  exact (tendsto_order.1 (hasDirichletDensity_iff.1 h)).2 (δ + ε) (by linarith)











end NumberField.Set

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Boolean calculus of Dirichlet density

For a number field `K`, Mathlib's `NumberField.Set.HasDirichletDensity S δ` says that

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s → δ` as `s → 1⁺`.

This file proves the elementary calculus of this predicate: uniqueness, the value `1` on all
primes, monotonicity, additivity on finite disjoint unions, complements, and two squeezes. The first
squeezes a set between two sets of the same density. The second is the finite-partition squeeze:
given a finite pairwise disjoint family whose union has `δ` as an *upper* density bound, lower
bounds on every member that already sum to `δ` leave no room, so each member's density is exactly
its bound. It also shows that one-sided density bounds move along inclusions of sets, which is
what makes the first squeeze work; the second rests instead on splitting the union's ratio exactly
and spending the summed lower bounds against it.

All of these are statements about the ratio for `s` close to `1` from the right, and on that
side both inputs they need are available: for `1 < s` each partial sum is a genuine sum rather
than the `tsum` junk value (`TauCeti.summable_absNorm_rpow_subtype_of_one_lt`), and the all-prime
denominator is positive (`NumberField.Set.primeIdealZetaSum_univ_pos_of_one_lt`). In particular
nothing here uses the divergence of the all-prime sum at `s = 1`. That divergence is what makes a
finite set of primes have density zero; the finite-error statements that use it are in
`TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible`.

## Main results

* `NumberField.Set.hasDirichletDensity_univ`: all primes have Dirichlet density `1`.
* `NumberField.Set.HasDirichletDensity.mono`: inclusion of prime sets orders their densities.
* `NumberField.Set.HasDirichletDensity.union` and
  `NumberField.Set.hasDirichletDensity_biUnion_finset`: Dirichlet density is additive on finite
  disjoint unions.
* `NumberField.Set.HasDirichletDensity.compl`: the complement of a set of density `δ` has
  density `1 - δ`.
* `NumberField.Set.IsLowerDirichletDensityBound.mono_set` and
  `NumberField.Set.IsUpperDirichletDensityBound.mono_set`: lower bounds pass to supersets and
  upper bounds to subsets.
* `NumberField.Set.hasDirichletDensity_of_subset_of_subset`: a set squeezed between two sets of
  density `δ` has density `δ`.
* `NumberField.Set.isUpperDirichletDensityBound_of_forall_isLowerDirichletDensityBound`: in a
  finite disjoint family whose union has `δ` as an upper density bound, lower bounds summing to
  `δ` bound each member from above as well.
* `NumberField.Set.hasDirichletDensity_of_squeeze`: hence each such
  member has density exactly its lower bound.

## References

* The declarations and proof structure are adapted from the `HasNaturalDensity` calculus in
  `TauCeti.NumberTheory.ArithmeticDirichletSeries.NaturalDensity`.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* The finite-partition squeeze is adapted from C. Birkbeck,
  [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/Abelian.lean`, whose
  `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` and `ratioSum_frobeniusFibres_tendsto_one`
  are the corresponding steps: the member-sum identity divided by the all-prime sum, and the
  `#s * ε` budget that turns the other members' lower bounds into this one's upper bound.
-/

 section

namespace NumberField.Set

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.NumberField _root_.Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T U : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}















/-- **Lower Dirichlet-density bounds pass to supersets.** -/
theorem IsLowerDirichletDensityBound.mono_set (hST : S ⊆ T)
    (hS : IsLowerDirichletDensityBound S δ) : IsLowerDirichletDensityBound T δ := by
  refine isLowerDirichletDensityBound_iff.2 fun η hη ↦ ?_
  filter_upwards [isLowerDirichletDensityBound_iff.1 hS η hη,
    self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
  exact hs.trans_le <| div_le_div_of_nonneg_right (primeIdealZetaSum_mono_set_of_one_lt hST hs1)
    (primeIdealZetaSum_nonneg _ s)

/-- **Upper Dirichlet-density bounds pass to subsets.** -/
theorem IsUpperDirichletDensityBound.mono_set (hST : S ⊆ T)
    (hT : IsUpperDirichletDensityBound T δ) : IsUpperDirichletDensityBound S δ := by
  refine isUpperDirichletDensityBound_iff.2 fun η hη ↦ ?_
  filter_upwards [isUpperDirichletDensityBound_iff.1 hT η hη,
    self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
  exact (div_le_div_of_nonneg_right (primeIdealZetaSum_mono_set_of_one_lt hST hs1)
    (primeIdealZetaSum_nonneg _ s)).trans_lt hs

/-- **Squeeze.** A set of primes lying between two sets of Dirichlet density `δ` has Dirichlet
density `δ`. -/
theorem hasDirichletDensity_of_subset_of_subset (hST : S ⊆ T) (hTU : T ⊆ U)
    (hS : HasDirichletDensity S δ) (hU : HasDirichletDensity U δ) :
    HasDirichletDensity T δ :=
  hasDirichletDensity_of_upperBound_of_lowerBound
    (hU.isUpperDirichletDensityBound.mono_set hTU)
    (hS.isLowerDirichletDensityBound.mono_set hST)









end NumberField.Set

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The residue degree of a height-one prime over `ℚ`

A height-one prime `𝔭` of `𝓞 K` lies over a unique rational prime `p`, and its absolute norm is
`p ^ f` for `f` the residue degree `Ideal.inertiaDeg 𝔭.asIdeal ℤ`.  This file names the two
objects that description involves and records their elementary theory.

## Main definitions

* `TauCeti.rationalPrimeBelow 𝔭` is the rational prime below a height-one prime `𝔭` of `𝓞 K`,
  namely the absolute norm of `𝔭 ∩ ℤ`.
* `TauCeti.higherDegreePrimes K` is the set of height-one primes of `𝓞 K` whose residue degree
  over `ℚ` exceeds `1`.
* `TauCeti.primesDividing K n hn` is the finite set of height-one primes of `𝓞 K` whose rational
  prime below divides a nonzero integer `n`.

## Main results

* `TauCeti.absNorm_eq_rationalPrimeBelow_pow`: the absolute norm of `𝔭` is the rational prime
  below it raised to the residue degree.
* `TauCeti.mem_higherDegreePrimes_iff_not_prime_absNorm`: a height-one prime has residue degree
  above one exactly when its absolute norm is not a prime number.
* `TauCeti.rationalPrimeBelow_pow_le_absNorm`: the norm of `𝔭` is at least the rational prime
  below it raised to any power at most the residue degree.
* `TauCeti.mem_higherDegreePrimes_of_one_lt_inertiaDeg`: residue degree above one over an
  intermediate number field forces residue degree above one over `ℚ`.
* `TauCeti.card_filter_rationalPrimeBelow_le_finrank`: at most `[K : ℚ]` height-one primes have
  a given rational prime below them.
* `IsDedekindDomain.HeightOneSpectrum.encard_setOf_under_eq_le_finrank`: at most `[E : K]`
  height-one primes of `E` contract to a given height-one prime of an intermediate number field
  `K`.
* `IsDedekindDomain.HeightOneSpectrum.absNorm_dvd_rationalPrimeBelow_pow_finrank`: the absolute
  norm of `𝔭` divides `p ^ [K : ℚ]`, so the residue degree is at most the degree of the field.
* `TauCeti.asIdeal_eq_span_singleton_of_absNorm_eq_pow_finrank`: a prime of full residue degree
  is inert, that is, generated by the rational prime below it.
* `IsDedekindDomain.HeightOneSpectrum.intCast_mem_asIdeal_iff`: an integer belongs to a
  height-one prime exactly when the rational prime below it divides that integer.
* `TauCeti.mem_primesDividing`: the defining condition for membership in `primesDividing`.

## Implementation notes

`rationalPrimeBelow` is named rather than spelled out as `Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal)`
because the estimates downstream fibre the primes over it: keeping it a single head symbol is what
makes the fibrewise rewriting elaborate, and it is the object `Chebotarev` will name when it
compares a prime of `K` with the rational prime under it.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §8.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]



omit [NumberField K] in
@[simp]
theorem mem_higherDegreePrimes {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ higherDegreePrimes K ↔ 1 < Ideal.inertiaDeg 𝔭.asIdeal ℤ :=
  Iff.rfl

/-! ### The rational prime below a height-one prime -/







omit [NumberField K] in
/-- The rational prime below a height-one prime really is a prime number. -/
theorem prime_rationalPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    (rationalPrimeBelow 𝔭).Prime := by
  have : NeZero 𝔭.asIdeal := ⟨𝔭.ne_bot⟩
  exact Nat.absNorm_under_prime 𝔭.asIdeal

/-- The absolute norm of a height-one prime is the rational prime below it raised to the residue
degree. -/
theorem absNorm_eq_rationalPrimeBelow_pow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔭.asIdeal =
      rationalPrimeBelow 𝔭 ^ Ideal.inertiaDeg 𝔭.asIdeal ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (Ideal.under ℤ 𝔭.asIdeal) 𝔭.asIdeal).symm



/-- The absolute norm of a height-one prime is at least the rational prime below it raised to any
exponent bounded by the residue degree.  The matching bound from above is the divisibility
`IsDedekindDomain.HeightOneSpectrum.absNorm_dvd_rationalPrimeBelow_pow_finrank`.  Use
`TauCeti.absNorm_eq_rationalPrimeBelow_pow` for the exact value instead, and
`TauCeti.mem_higherDegreePrimes` to supply the hypothesis at the common instance `n = 2`. -/
theorem rationalPrimeBelow_pow_le_absNorm {𝔭 : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (hn : n ≤ Ideal.inertiaDeg 𝔭.asIdeal ℤ) : rationalPrimeBelow 𝔭 ^ n ≤ Ideal.absNorm 𝔭.asIdeal :=
  -- the norm is `p ^ f`, and `p` is at least `2`, so the power is monotone in the exponent
  absNorm_eq_rationalPrimeBelow_pow 𝔭 ▸
    Nat.pow_le_pow_right (prime_rationalPrimeBelow 𝔭).one_lt.le hn

/-- A height-one prime of `𝓞 E` whose residue degree over a number field `K` below `E` exceeds one
has residue degree above one over `ℚ`, since residue degrees multiply along `ℤ → 𝓞 K → 𝓞 E`. -/
theorem mem_higherDegreePrimes_of_one_lt_inertiaDeg {E : Type*} [Field E] [Algebra K E]
    {𝔓 : HeightOneSpectrum (𝓞 E)} (h : 1 < 𝔓.asIdeal.inertiaDeg (𝓞 K)) :
    𝔓 ∈ higherDegreePrimes E := by
  rw [mem_higherDegreePrimes, Ideal.inertiaDeg_tower (R := ℤ) (𝔓.asIdeal.under (𝓞 K)) 𝔓.asIdeal]
  have := Ideal.inertiaDeg_pos (𝔓.asIdeal.under (𝓞 K)) ℤ
  nlinarith

/-! ### Fibring the primes over the rational primes below them -/





/-! ### Inert primes -/







/-! ### The primes dividing an integer -/









end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The primes of residue degree above one are negligible

A height-one prime `𝔭` of `𝓞 K` lies over a unique rational prime `p`, and its absolute norm is
`p ^ f` for `f` the residue degree `Ideal.inertiaDeg 𝔭.asIdeal ℤ`.  This file bounds the
contribution of the primes with `f ≥ 2`, the set `TauCeti.higherDegreePrimes K`: they number
`O(√x)` up to norm `x`, hence also `o(x / log x)`, and their Dirichlet series `∑ N(𝔭) ^ (-s)`
converges for every `s > 1/2`, with a bound that is uniform on `s ≥ 1`.

Two elementary inputs carry the whole argument.

* A prime with `f ≥ 2` has `N(𝔭) = p ^ f ≥ p ^ 2`, so it is *not* determined by a rational prime
  of size `N(𝔭)` but by one of size at most `√(N(𝔭))`.
* At most `[K : ℚ]` height-one primes lie over one rational prime, by the fundamental identity
  `∑ e f = [K : ℚ]`; this is the already available
  `TauCeti.card_filter_rationalPrimeBelow_le_finrank`, itself resting on
  `TauCeti.NumberField.card_primesOverFinset_le_finrank`.

Together these compare any finite sum over the degree-above-one primes with `[K : ℚ]` times a sum
over the rational primes with the exponent doubled, which is
`TauCeti.sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum` below.  Counting gives the
`O(√x)` bound, and summing `m ^ (-2s)` gives convergence for every `s > 1/2` together with a
bound on the partial Dirichlet series that is *uniform* on `s ≥ 1`.

## Main results

* `TauCeti.primeCount_higherDegreePrimes_le`: the explicit count
  `π_K(x; f ≥ 2) ≤ [K : ℚ] · √x`, with `TauCeti.primeCount_higherDegreePrimes_isBigO` and
  `TauCeti.primeCount_higherDegreePrimes_isLittleO` its `O(√x)` and `o(x / log x)` forms.
* `TauCeti.summable_absNorm_rpow_higherDegreePrimes`: `∑ N(𝔭) ^ (-s)` over the degree-above-one
  primes converges for every `s > 1/2`, in particular at `s = 1`.
* `TauCeti.primeTheta_higherDegreePrimes_isLittleO`: those primes carry weight `o(x)` in `ϑ_K`.
* `TauCeti.primeIdealZetaSum_higherDegreePrimes_le`: that sum, in Mathlib's
  `NumberField.Set.primeIdealZetaSum` vocabulary, is at most `2 [K : ℚ]` for every `s ≥ 1`.
* `TauCeti.sum_absNorm_rpow_le_finrank_mul_tsum` and
  `TauCeti.tsum_absNorm_rpow_le_finrank_mul_tsum`: the same fibring over *all* height-one primes,
  in finite and infinite form, for every `s > 1`.
* `TauCeti.tsum_absNorm_rpow_neg_two_le`: at `s = 2` that becomes the explicit
  `∑_𝔭 N(𝔭) ^ (-2) ≤ 2 [K : ℚ]`.

No density-zero statement is proved here.  What this file supplies is the numerator half of
one: `NumberField.Set.HasDirichletDensity (higherDegreePrimes K) 0` asks for
`primeIdealZetaSum (higherDegreePrimes K) s / primeIdealZetaSum univ s → 0` as `s → 1⁺`, and the
bound below controls only the numerator.  Together with the divergence of the denominator it gives
`TauCeti.hasDirichletDensity_higherDegreePrimes` in
`TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible`.  By contrast
`primeCount K (higherDegreePrimes K) =o[atTop] primeCount K univ`
would need a lower bound on the full prime count, which the prime ideal theorem supplies and
which is not available here; the `o(x / log x)` statement below is against the explicit
function `x / log x`, not against `π_K`.

## Implementation notes

The set `TauCeti.higherDegreePrimes` and the map `TauCeti.rationalPrimeBelow` the estimates fibre
over, together with their elementary norm and inertia theory, are algebraic rather than analytic
and live in `TauCeti.NumberTheory.NumberField.ResidueDegree`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, and J. Milne, *Algebraic Number Theory*,
  Chapter VIII, for the same estimate in the Dirichlet-density setting.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-! ### Fibring a sum over the rational primes below the primes -/

/-- Comparison of a finite sum over height-one primes with a sum over the rational primes below
them: the fibres have at most `[K : ℚ]` elements. -/
theorem sum_comp_rationalPrimeBelow_le {g : ℕ → ℝ} {F : Finset (HeightOneSpectrum (𝓞 K))}
    {T : Finset ℕ} (hg : ∀ m ∈ T, 0 ≤ g m) (hFT : ∀ 𝔭 ∈ F, rationalPrimeBelow 𝔭 ∈ T) :
    ∑ 𝔭 ∈ F, g (rationalPrimeBelow 𝔭) ≤ Module.finrank ℚ K * ∑ m ∈ T, g m := by
  rw [← Finset.sum_fiberwise_of_maps_to' hFT g, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm ↦ ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (mod_cast card_filter_rationalPrimeBelow_le_finrank F m) (hg m hm)

/-- Comparison of a finite sum over height-one primes with the *whole* sum over `ℕ`: fibring
costs a factor `[K : ℚ]`, and completing the finite rational-prime sum to its `tsum` costs
nothing because the summand is nonnegative. This is the shape both norm-sum bounds below
take, once each has compared its own summand termwise with `g (rationalPrimeBelow 𝔭)`. -/
theorem sum_comp_rationalPrimeBelow_le_finrank_mul_tsum {g : ℕ → ℝ} (hg : ∀ m, 0 ≤ g m)
    (hsum : Summable g) (F : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ 𝔭 ∈ F, g (rationalPrimeBelow 𝔭) ≤ Module.finrank ℚ K * ∑' m : ℕ, g m :=
  (sum_comp_rationalPrimeBelow_le (fun m _ ↦ hg m)
        fun _ ↦ Finset.mem_image_of_mem rationalPrimeBelow).trans
    (mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun m _ ↦ hg m) (Nat.cast_nonneg _))

/-! ### Counting the primes of residue degree above one -/











/-! ### Convergence of the prime Dirichlet series over the degree-above-one primes -/




/-- The Dirichlet series over the primes of residue degree above one converges for every
`s > 1/2`, in particular at `s = 1`. -/
theorem summable_absNorm_rpow_higherDegreePrimes {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun 𝔭 : higherDegreePrimes K ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
  classical
  refine summable_of_sum_le (c := Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)))
    (fun 𝔭 ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _) fun u ↦ ?_
  have := sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum (K := K) hs
    (F := u.image Subtype.val) (fun 𝔭 h𝔭 ↦ by
      obtain ⟨𝔮, -, rfl⟩ := Finset.mem_image.mp h𝔭
      exact 𝔮.2)
  rwa [Finset.sum_image fun _ _ _ _ h ↦ Subtype.ext h] at this



/-! ### All height-one primes -/

/-- **A finite norm sum is at most `[K : ℚ]` times the sum of `m ^ (-s)` over `ℕ`.** Fibring a
finite sum of `N(𝔭) ^ (-s)` over the rational primes below costs a factor `[K : ℚ]`. Without a
residue-degree hypothesis only `p ≤ N(𝔭)` is available, so the exponent stays `-s` and the
argument needs `1 < s`; the degree-above-one analogue
`TauCeti.sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum` gains the exponent `-2s` and so
reaches down to `s > 1/2`. -/
theorem sum_absNorm_rpow_le_finrank_mul_tsum {s : ℝ} (hs : 1 < s)
    (F : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ 𝔭 ∈ F, (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-s) :=
  (Finset.sum_le_sum fun 𝔭 _ ↦ by
        have hpN : rationalPrimeBelow 𝔭 ≤ Ideal.absNorm 𝔭.asIdeal := by
          simpa using rationalPrimeBelow_pow_le_absNorm (𝔭.asIdeal.inertiaDeg_pos ℤ)
        exact Real.rpow_le_rpow_of_nonpos (mod_cast (prime_rationalPrimeBelow 𝔭).pos)
          (mod_cast hpN) (by linarith)).trans
    (sum_comp_rationalPrimeBelow_le_finrank_mul_tsum
      (fun m ↦ Real.rpow_nonneg (Nat.cast_nonneg m) _)
      (Real.summable_nat_rpow.mpr (by linarith)) F)

/-- **The prime ideal zeta sum is at most `[K : ℚ]` times the sum of `m ^ (-s)` over `ℕ`.** The
finite-sum comparison passes to the limit on the whole range `1 < s` where both sides converge.
Specializing the exponent is what buys an explicit constant, as in
`TauCeti.tsum_absNorm_rpow_neg_two_le`. -/
theorem tsum_absNorm_rpow_le_finrank_mul_tsum {s : ℝ} (hs : 1 < s) :
    ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-s) :=
  Real.tsum_le_of_sum_le (fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (sum_absNorm_rpow_le_finrank_mul_tsum hs)

/-- **The prime ideal zeta sum over all height-one primes at `s = 2` is at most `2 [K : ℚ]`.**
At most `[K : ℚ]` primes lie over each rational prime, and `ζ (2) < 2`.  The same constant bounds
the degree-above-one primes for every `s ≥ 1`: `TauCeti.primeIdealZetaSum_higherDegreePrimes_le`.
The constant is available only from `s = 2` upwards: at `s` just above `1` the sum over `ℕ` is
already larger than `2`, so only the `s`-dependent bound above survives there. -/
theorem tsum_absNorm_rpow_neg_two_le :
    ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)) ≤
      2 * Module.finrank ℚ K :=
  ((tsum_absNorm_rpow_le_finrank_mul_tsum one_lt_two).trans <| mul_le_mul_of_nonneg_left
    (tsum_nat_rpow_neg_le_two le_rfl) (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)

end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The real Euler product of the Dedekind zeta function in exponential form

For real `s > 1`, every local ratio `x = N(𝔭) ^ (-s)` of a height-one prime lies in `(0, 1/2]`,
because `N(𝔭) ≥ 2`. The principal logarithm of each Euler factor is then the real number
`-log (1 - x)`, and the exponential form
`TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries` of the Euler product,
specialized to the trivial weight, becomes a statement about real numbers: `ζ_K(s)` is the
exponential of the convergent real sum `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`. In particular `ζ_K(s)` is a
positive real number, and that sum is its real logarithm.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.absNorm_rpow_neg_le_half`: `N(𝔭) ^ (-s) ≤ 1/2`
  for `1 ≤ s`.
* `TauCeti.summable_neg_log_one_sub_absNorm_rpow`: `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` converges for
  `1 < s`.
* `TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub`: for real `s > 1`, `ζ_K(s)` is the
  exponential of that real sum.
* `TauCeti.dedekindZeta_re_eq_exp` and `TauCeti.dedekindZeta_re_pos`: the same for the real part,
  which is therefore positive.
* `TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`: that real sum is the real logarithm of
  `ζ_K(s)`.

## References

* The real logarithmic identity also appears, under the same name, in the
  Birkbeck–Brasca Chebotarev density project, <https://github.com/CBirkbeck/chebotarev-density>
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/Density.lean`, where it is proved from `Real.hasProd_of_hasSum_log` and the
  product formula. It is derived here instead from TauCeti's exponential Euler product
  `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- For `1 ≤ s`, the local ratio `N(𝔭) ^ (-s)` of a height-one prime is at most `1/2`, because
`N(𝔭) ≥ 2`. -/
theorem absNorm_rpow_neg_le_half (P : HeightOneSpectrum (𝓞 K)) {s : ℝ} (hs : 1 ≤ s) :
    (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 :=
  Real.rpow_neg_le_half (TauCeti.two_le_absNorm_asIdeal_real P) hs

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- For `1 < s`, the real logarithms `-log (1 - N(𝔭) ^ (-s))` of the Euler factors of the Dedekind
zeta function are summable over the height-one primes. -/
theorem summable_neg_log_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := by
  refine ((summable_absNorm_rpow_primes_of_one_lt hs).mul_left 2).of_nonneg_of_le
    (fun P ↦ (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (by
      have hpos : 0 < 1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
        linarith [P.absNorm_rpow_neg_le_half hs.le]
      linarith [Real.log_le_sub_one_of_pos hpos])) (fun P ↦ ?_)
  -- On `[0, 1/2]`, `x + 2 x ^ 2 ≤ 2 x`.
  have hx0 : 0 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by positivity
  have hx := P.absNorm_rpow_neg_le_half hs.le
  nlinarith [Real.neg_log_one_sub_le_add_two_mul_sq hx0 hx]



/-- For real `s > 1`, the real part of `ζ_K(s)` is the exponential of `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`.
-/
theorem dedekindZeta_re_eq_exp {s : ℝ} (hs : 1 < s) :
    (dedekindZeta K s).re = Real.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))) := by
  rw [dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub hs, Complex.ofReal_re]

/-- **The real logarithm of the Dedekind zeta function.** For real `s > 1`, the real logarithm of
`ζ_K(s)` is the convergent sum `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` over the height-one primes of `𝓞 K`.
-/
theorem log_dedekindZeta_re_eq_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K s).re = ∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := by
  rw [dedekindZeta_re_eq_exp hs, Real.log_exp]



end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The higher prime powers in the logarithm of the Dedekind Euler product

Taking logarithms in the Euler product `ζ_K(s) = ∏_𝔭 (1 - N(𝔭) ^ (-s))⁻¹` turns it into the
double sum `∑_𝔭 ∑_{m ≥ 1} N(𝔭) ^ (-m s) / m`, whose `m = 1` part is the prime Dirichlet series
`NumberField.Set.primeIdealZetaSum Set.univ s`.  This file bounds everything else: the `m ≥ 2`
part, equivalently the difference `∑_𝔭 (-log (1 - N(𝔭) ^ (-s)) - N(𝔭) ^ (-s))`, is nonnegative
and at most `2 [K : ℚ]`.

The bound is uniform on all of `s ≥ 1`, endpoint included, and that endpoint is the whole point:
at `s = 1` the Euler-factor logarithm sum and the prime Dirichlet series each diverge, while
their termwise difference still converges, because discarding the linear term of
`-log (1 - x)` replaces the exponent `-s` by the exponent `-2 s`, and `2 s ≥ 2` already
converges.

Two elementary inputs carry the argument.

* A height-one prime `𝔭` has `N(𝔭) ≥ 2`, so `N(𝔭) ^ (-s) ≤ 1 / 2` for `s ≥ 1` and the
  denominator `1 - N(𝔭) ^ (-s)` is bounded below by `1 / 2`; the termwise difference is
  therefore at most `N(𝔭) ^ (-2)`.
* `N(𝔭)` is at least the rational prime below `𝔭` and at most `[K : ℚ]` primes lie over one
  rational prime, so `∑_𝔭 N(𝔭) ^ (-2) ≤ 2 [K : ℚ]`.  That bound is not proved again here: it is
  the imported `TauCeti.tsum_absNorm_rpow_neg_two_le`.

## Main results

* `TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow`: the termwise difference between the
  Euler-factor logarithm and the prime Dirichlet term is summable for every `s > 1 / 2`.
* `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg`: termwise nonnegativity for `s > 0`
  yields a nonnegative `tsum`; convergence is supplied separately for `s > 1 / 2`.
* `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le`: it is at most `2 [K : ℚ]` for every
  `s ≥ 1`; together the two bound the sum in `[0, 2 [K : ℚ]]` on `s ≥ 1`.
* `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le`: for `s > 1`, where the
  two sums converge separately, the sum of the Euler-factor logarithms differs from
  `NumberField.Set.primeIdealZetaSum Set.univ s` by at most `2 [K : ℚ]`.

## Implementation notes

The constant is explicit rather than existentially quantified, and the upper bound's hypothesis
is the closed condition `1 ≤ s` rather than a neighbourhood of `1`: both are free here, and a
consumer that wants an eventual statement near `s = 1` gets it by weakening, whereas the
converse costs work.

The two halves carry different hypotheses on purpose. Nonnegativity holds as soon as
`N(𝔭) ^ (-s) < 1`, so it is stated on `0 < s`; the uniform upper bound uses
`N(𝔭) ^ (-s) ≤ 1 / 2`. No uniform bound can persist as `s ↓ 1 / 2`, where the dominating
prime series approaches its convergence endpoint.

The one-variable estimate behind the termwise bound is not proved again: it is Mathlib's
`Complex.norm_log_one_sub_inv_sub_self_le` read along the reals, which is where the factor `2`
in the denominator below comes from.

Convergence of `∑_𝔭 N(𝔭) ^ (-s)` over all height-one primes for `1 < s` is not proved again
either: it is `TauCeti.summable_absNorm_rpow_primes_of_one_lt`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §3.
* C. Birkbeck and R. Brasca, `CebotarevDensity/Density.lean` in
  [CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density), Apache-2.0,
  commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, declarations
  `primeIdealZetaHigherTail_bounded` and `neg_log_one_sub_sub_le`.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-! ### The prime-power tail -/

/-- **The prime-power tail is summable.** The termwise difference between the Euler-factor
logarithm `-log (1 - N(𝔭) ^ (-s))` and the prime Dirichlet term `N(𝔭) ^ (-s)` is summable for
every `s > 1 / 2`; at `s = 1` this remains summable although either of the two families from which
it is built is not. -/
theorem summable_neg_log_one_sub_sub_absNorm_rpow {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  have hs0 : 0 < s := by linarith
  have hs2 : 1 < 2 * s := by linarith
  have hsum := (summable_absNorm_rpow_primes_of_one_lt (K := K) hs2).mul_left
    ((2 * (1 - (2 : ℝ) ^ (-s)))⁻¹)
  refine hsum.of_nonneg_of_le
    (fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_nonneg
      (one_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭)) hs0) ?_
  intro 𝔭
  simpa only [div_eq_mul_inv, mul_comm] using
    Real.neg_log_one_sub_rpow_sub_le_div (two_le_absNorm_asIdeal_real 𝔭) hs0

/-- **The prime-power tail is termwise nonnegative.** For every `s > 0`, termwise nonnegativity
yields a nonnegative `tsum`. This statement does not assert summability; that is supplied by
`TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow` for `s > 1 / 2`. -/
theorem tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg {s : ℝ} (hs : 0 < s) :
    0 ≤ ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
  tsum_nonneg fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_nonneg
    (one_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭)) hs

/-- **The prime-power tail is bounded uniformly on `s ≥ 1`.** The constant `2 [K : ℚ]` does not
depend on `s`, so this survives the passage to the limit `s → 1⁺` that the Dirichlet-density
normalization needs. -/
theorem tsum_neg_log_one_sub_sub_absNorm_rpow_le {s : ℝ} (hs : 1 ≤ s) :
    ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ≤ 2 * Module.finrank ℚ K :=
  ((summable_neg_log_one_sub_sub_absNorm_rpow (K := K)
      ((by norm_num : (1 / 2 : ℝ) < 1).trans_le hs)).tsum_le_tsum
    (fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_le (two_le_absNorm_asIdeal_real 𝔭) hs)
    (summable_absNorm_rpow_primes_of_one_lt one_lt_two)).trans tsum_absNorm_rpow_neg_two_le

/-- **The Euler-factor logarithms sum to the prime Dirichlet series up to `O(1)`.** For `s > 1`,
where both series converge, `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` differs from
`NumberField.Set.primeIdealZetaSum Set.univ s` by at most the constant `2 [K : ℚ]`.

The absolute value is here so that the statement can be used directly as an `O(1)` estimate; the
difference is in fact nonnegative — see `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg`. -/
theorem abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le {s : ℝ} (hs : 1 < s) :
    |(∑' 𝔭 : HeightOneSpectrum (𝓞 K), -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) -
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s| ≤ 2 * Module.finrank ℚ K := by
  have hsumP := TauCeti.summable_absNorm_rpow_primes_of_one_lt (K := K) hs
  have hsumL : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
    simpa using (TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow (K := K)
      ((by norm_num : (1 / 2 : ℝ) < 1).trans hs)).add hsumP
  -- Both series converge separately, so their difference is the sum of the prime-power tail.
  rw [NumberField.Set.primeIdealZetaSum_def, tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s), ← hsumL.tsum_sub hsumP,
    abs_of_nonneg (TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg (zero_lt_one.trans hs))]
  exact TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le hs.le

end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The all-prime Dirichlet sum is `log (1 / (s - 1)) + O(1)`

For a number field `K`, write `P(s) = ∑_𝔭 N(𝔭) ^ (-s)` for the sum over all height-one primes of
`𝓞 K`, which is `NumberField.Set.primeIdealZetaSum Set.univ s`. This file proves that
`P(s) = log (1 / (s - 1)) + O(1)` as `s → 1⁺`, and hence that Mathlib's ratio-normalized
`NumberField.Set.HasDirichletDensity` agrees with the logarithmically normalized density.

The proof has two inputs, and neither suffices alone.

* **The Euler product.** For real `s > 1`, `log ζ_K(s)` is the convergent sum
  `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`, by `TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`.
  The higher-prime-power tail theorem
  `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le` bounds the difference from `P(s)`
  by `2 [K : ℚ]`, uniformly for `s > 1`.
* **The residue.** Mathlib's class number formula
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` says that `(s - 1) ζ_K(s)` tends to the
  positive residue as `s → 1⁺`, so `log ζ_K(s) - log (1 / (s - 1))` tends to its logarithm.

## Main results

* `TauCeti.primeIdealZetaSum_univ_le_log_dedekindZeta_re` and
  `TauCeti.log_dedekindZeta_re_le_primeIdealZetaSum_univ_add`: the two-sided comparison of
  `log ζ_K(s)` with `P(s)`, with error at most `2 [K : ℚ]`.
* `TauCeti.tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one`: `log ζ_K(s) - log (1 / (s - 1))`
  tends to the logarithm of the residue.
* `TauCeti.primeIdealZetaSum_univ_sub_log_one_div_sub_one_isBigO`:
  `P(s) - log (1 / (s - 1)) = O(1)` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_atTop`: `P(s) → ∞` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_div_log_one_div_sub_one`:
  `P(s) / log (1 / (s - 1)) → 1` as `s → 1⁺`.
* `NumberField.Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one`: a set of primes has
  Dirichlet density `δ` exactly when `P_S(s) / log (1 / (s - 1)) → δ`.
* `NumberField.Set.ofReal_primeIdealZetaSum`: `P_S(t)`, cast to `ℂ`, is the complex sum over all
  primes of the indicator of `S` against `N(𝔭) ^ (-t)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* The same argument (Sharifi, *Algebraic Number Theory*, 7.1.12) is formalized in the
  Birkbeck–Brasca Chebotarev density project, <https://github.com/CBirkbeck/chebotarev-density>
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/Density.lean`: `primeIdealZetaSum_univ_tendsto_log` and
  `primeIdealZetaSum_univ_tendsto_atTop`, closed there by the helpers of
  `CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` that `Real.tendsto_log_one_div_sub_atTop`
  and `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le` adapt. This file follows
  its outline (Euler-product logarithm, bounded higher-prime-power contribution, simple pole),
  over `HeightOneSpectrum` rather than the nonzero prime ideals of `𝓞 K`. It derives the
  logarithmic form of the Euler product from
  `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries` and uses the explicit
  higher-prime-power bound from
  `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le`.
-/

 section

open _root_.Filter _root_.Asymptotics _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.Topology

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **The prime sum is at most `log ζ_K(s)`.** For real `s > 1`, the sum of `N(𝔭) ^ (-s)` over all
height-one primes is at most the real logarithm of `ζ_K(s)`. -/
theorem primeIdealZetaSum_univ_le_log_dedekindZeta_re {s : ℝ} (hs : 1 < s) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s ≤
      Real.log (dedekindZeta K s).re := by
  rw [log_dedekindZeta_re_eq_tsum_neg_log_one_sub hs, Set.primeIdealZetaSum_univ]
  exact (summable_absNorm_rpow_primes_of_one_lt hs).tsum_le_tsum
    (fun P ↦ by
      have hpos : 0 < 1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
        linarith [P.absNorm_rpow_neg_le_half hs.le]
      linarith [Real.log_le_sub_one_of_pos hpos])
    (summable_neg_log_one_sub_absNorm_rpow hs)

/-- **`log ζ_K(s)` exceeds the prime sum by at most `2 [K : ℚ]`.** For real `s > 1`, the real
logarithm of `ζ_K(s)` is at most the all-prime sum at `s` plus `2 [K : ℚ]`, a constant independent
of `s` that bounds the contribution of the higher prime powers. -/
theorem log_dedekindZeta_re_le_primeIdealZetaSum_univ_add {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K s).re ≤
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s +
        2 * Module.finrank ℚ K := by
  rw [log_dedekindZeta_re_eq_tsum_neg_log_one_sub hs]
  have h := (abs_le.mp
    (abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le (K := K) hs)).2
  linarith

/-! ### The residue and the logarithmic normalization -/



/-- The all-prime sum stays within a bounded distance of `log (1 / (s - 1))` near `1⁺`. -/
private theorem exists_abs_primeIdealZetaSum_univ_sub_log_one_div_sub_one_le :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      |(Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s -
        Real.log (1 / (s - 1))| ≤ C := by
  refine ⟨|Real.log (dedekindZeta_residue K)| + 1 +
    2 * Module.finrank ℚ K, ?_⟩
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K s).re - Real.log (1 / (s - 1))| ≤
        |Real.log (dedekindZeta_residue K)| + 1 := by
    refine (tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one (K := K)).abs.eventually
      (ge_mem_nhds ?_)
    linarith
  filter_upwards [hnear, self_mem_nhdsWithin] with s hnear hs
  have h1 := primeIdealZetaSum_univ_le_log_dedekindZeta_re (K := K) hs
  have h2 := log_dedekindZeta_re_le_primeIdealZetaSum_univ_add (K := K) hs
  have h3 : (0 : ℝ) ≤ 2 * Module.finrank ℚ K := by positivity
  rw [abs_le] at hnear ⊢
  constructor <;> linarith [hnear.1, hnear.2]



/-- **The all-prime sum diverges at `1`.** The sum of `N(𝔭) ^ (-s)` over all height-one primes of
`𝓞 K` tends to `+∞` as `s → 1⁺`. -/
theorem tendsto_primeIdealZetaSum_univ_atTop :
    Tendsto (fun s : ℝ ↦ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)
      (𝓝[>] 1) atTop := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_univ_sub_log_one_div_sub_one_le (K := K)
  refine tendsto_atTop_mono' _ (hC.mono fun s hs ↦ ?_)
    (tendsto_atTop_add_const_right _ (-C) (Real.tendsto_log_one_div_sub_atTop 1))
  linarith [(abs_le.mp hs).1]



end TauCeti

namespace NumberField.Set

open _root_.TauCeti

variable {K : Type*} [Field K] [NumberField K]





end NumberField.Set

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
namespace TauCeti.NumberField
end TauCeti.NumberField
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Sets of primes of Dirichlet density zero

For a number field `K`, Mathlib's `NumberField.Set.HasDirichletDensity S δ` says that
`P_S(s) / P(s) → δ` as `s → 1⁺`, where `P_S(s) = ∑_{𝔭 ∈ S} N(𝔭) ^ (-s)` and `P` is the sum over
all height-one primes. Since `P(s) → ∞` as `s → 1⁺`
(`TauCeti.tendsto_primeIdealZetaSum_univ_atTop`), any set whose partial sum stays bounded near
`1` has Dirichlet density zero. This covers every finite set of primes, and every set whose
series `∑_{𝔭 ∈ S} N(𝔭)⁻¹` converges, such as the primes of residue degree greater than one.

A set of density zero is negligible: two sets whose symmetric difference has density zero have
the same Dirichlet density, or neither has one. In particular the Dirichlet density of a set of
primes does not change when finitely many primes are added or removed, or when the set is
restricted to the primes of residue degree one.

## Main results

* `NumberField.Set.hasDirichletDensity_zero_of_eventually_le`: a set whose partial sum is bounded
  as `s → 1⁺` has Dirichlet density zero.
* `NumberField.Set.hasDirichletDensity_zero_of_summable`: a set of primes with
  `∑_{𝔭 ∈ S} N(𝔭)⁻¹ < ∞` has Dirichlet density zero.
* `NumberField.Set.hasDirichletDensity_of_finite`: a finite set of primes has Dirichlet density
  zero, so a set of nonzero Dirichlet density is infinite
  (`NumberField.Set.HasDirichletDensity.infinite`).
* `NumberField.Set.hasDirichletDensity_iff_of_symmDiff`: sets whose symmetric difference has
  density zero have the same densities; `NumberField.Set.hasDirichletDensity_iff_of_finite_symmDiff`
  is the case of a finite symmetric difference.
* `TauCeti.hasDirichletDensity_higherDegreePrimes`: the primes of residue degree greater than one
  have Dirichlet density zero, and
  `TauCeti.hasDirichletDensity_inter_compl_higherDegreePrimes_iff` lets a density be computed on
  the primes of residue degree one alone.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

 section

namespace NumberField.Set

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.NumberField _root_.TauCeti.NumberField _root_.symmDiff _root_.Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

/-- **A bounded partial sum gives density zero.** If `P_S(s) ≤ C` for all `s` close enough to `1`
from the right, then `S` has Dirichlet density zero, because the all-prime denominator tends to
infinity. -/
theorem hasDirichletDensity_zero_of_eventually_le {C : ℝ}
    (h : ∀ᶠ s in 𝓝[>] (1 : ℝ), S.primeIdealZetaSum s ≤ C) : S.HasDirichletDensity 0 := by
  have hP := tendsto_primeIdealZetaSum_univ_atTop (K := K)
  refine hasDirichletDensity_iff.2 <| tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds ((tendsto_const_nhds (x := C)).div_atTop hP) ?_ ?_
  · filter_upwards with s
    exact div_nonneg (S.primeIdealZetaSum_nonneg s) (Set.univ.primeIdealZetaSum_nonneg s)
  · filter_upwards [h, hP.eventually_gt_atTop 0] with s hs hpos
    exact div_le_div_of_nonneg_right hs hpos.le

/-- **A convergent reciprocal-norm series gives density zero.** If `∑_{𝔭 ∈ S} N(𝔭)⁻¹` converges,
then `S` has Dirichlet density zero: for `s ≥ 1` every term `N(𝔭) ^ (-s)` is at most `N(𝔭)⁻¹`,
so the partial sums stay bounded as `s → 1⁺`. -/
theorem hasDirichletDensity_zero_of_summable
    (h : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-1 : ℝ)) :
    S.HasDirichletDensity 0 := by
  refine hasDirichletDensity_zero_of_eventually_le (C := S.primeIdealZetaSum 1) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have hle : ∀ 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) ≤
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-1 : ℝ) := fun 𝔭 ↦
    Real.rpow_le_rpow_of_exponent_le (one_le_absNorm_real_of_nonZeroDivisors
      ⟨𝔭.1.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.1.ne_bot⟩) (by linarith)
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  exact (h.of_nonneg_of_le (fun _ ↦ by positivity) hle).tsum_le_tsum hle h





/-- **Subsets of sets of density zero have density zero.** -/
theorem HasDirichletDensity.zero_of_subset (hT : T.HasDirichletDensity 0) (hST : S ⊆ T) :
    S.HasDirichletDensity 0 :=
  hasDirichletDensity_of_subset_of_subset (Set.empty_subset S) hST hasDirichletDensity_empty hT



/-- Two sets of primes whose symmetric difference has Dirichlet density zero have the same
Dirichlet densities. -/
theorem hasDirichletDensity_iff_of_symmDiff (h : (S ∆ T).HasDirichletDensity 0) :
    S.HasDirichletDensity δ ↔ T.HasDirichletDensity δ :=
  ⟨fun hS ↦ hS.of_symmDiff (symmDiff_comm S T ▸ h), fun hT ↦ hT.of_symmDiff h⟩







end NumberField.Set

open _root_.IsDedekindDomain _root_.NumberField _root_.NumberField.Set

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **The primes of residue degree greater than one have Dirichlet density zero**, because their
reciprocal-norm series converges. -/
theorem hasDirichletDensity_higherDegreePrimes : (higherDegreePrimes K).HasDirichletDensity 0 :=
  hasDirichletDensity_zero_of_summable (summable_absNorm_rpow_higherDegreePrimes (by norm_num))





end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Contracting prime sums and Dirichlet densities along a fibre count

Let `K` and `E` be number fields, `T` a set of height-one primes of `𝓞 E` and `S` one of `𝓞 K`,
and let `π` send each prime of `E` to a prime of `K`. Suppose that `π` maps `T` into `S`, that it
preserves absolute norms on `T`, and that every `𝔭 ∈ S` has exactly `c ≠ 0` preimages in `T`.
Then, for every real `s`,

```text
∑_{𝔓 ∈ T} N𝔓 ^ (-s) = c * ∑_{𝔭 ∈ S} N𝔭 ^ (-s),
```

and consequently `T` has Dirichlet density `δ` exactly when `S` has Dirichlet density `δ / c`.

The fibre count only matters away from a set of density zero. If `π` does not increase norms and
has boundedly many preimages in `T` over each prime of `S`, the prime sum over `T` is bounded by a
multiple of the prime sum over `S`, so preimages of a density-zero set have density zero. Hence the
exact count `c` is needed only for the primes of `S` outside a density-zero set `Z`, with a
uniform bound over `Z`.

The typical `π` is contraction `𝔓 ↦ 𝔓 ∩ 𝓞 K` for an extension `E / K`. It preserves norms exactly
on the primes of residue degree one over `K`, and the others have density zero, so only primes of
residue degree one need to be counted in the fibres; at most `[E : K]` primes of `E` lie over a
given prime of `K`, which supplies the uniform bound over `Z`. This is how a density computed over
an extension field is transported down to the base, as in the proof of the Chebotarev density
theorem, where a relative Frobenius fibre over the fixed field of a cyclic subgroup is counted
over the primes of the base field.

## Main results

* `NumberField.Set.primeIdealZetaSum_eq_mul_of_card_fiber`: the exact identity of prime sums.
* `NumberField.Set.hasDirichletDensity_iff_of_card_fiber`: the transfer of Dirichlet densities.
* `NumberField.Set.primeIdealZetaSum_le_mul_of_encard_fiber_le`: the prime-sum inequality for a
  bounded fibre count.
* `NumberField.Set.HasDirichletDensity.zero_of_encard_fiber_le`: density zero pulls back along a
  bounded fibre count.
* `NumberField.Set.hasDirichletDensity_iff_of_card_fiber_of_negligible`: the transfer of
  Dirichlet densities when the fibre count is exact only off a set of density zero.
* `NumberField.Set.hasDirichletDensity_contraction`: the transfer along contraction, counting only
  primes of residue degree one and only off a set of density zero.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
-/

 section

open Filter IsDedekindDomain NumberField
open scoped symmDiff Topology

namespace NumberField.Set
end NumberField.Set
section NumberField.Set
open NumberField NumberField.Set

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
  {T : Set (HeightOneSpectrum (𝓞 E))} {S : Set (HeightOneSpectrum (𝓞 K))}
  {π : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 K)} {c : ℕ}











/-- **Dirichlet densities along contraction.** Let `E / K` be an extension of number fields, `T` a
set of primes of `E` whose residue-degree-one members outside the preimage of `Z` contract into a
set `S` of primes of `K`, and `Z` a set of primes of `K` of Dirichlet density zero. If every prime
of `S` outside `Z` lies below exactly `c ≠ 0` members of `T` of residue degree one over `K`, then
`T` has Dirichlet density `δ` exactly when `S` has Dirichlet density `δ / c`.

Neither the primes of `T` of residue degree above one over `K` nor those over `Z` need to be
counted: both form sets of density zero. -/
theorem solution [_root_.Algebra K E] {Z : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    (hZ : Z.HasDirichletDensity 0)
    (hmaps : ∀ 𝔓 ∈ T, 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1 → 𝔓.under (𝓞 K) ∉ Z →
      𝔓.under (𝓞 K) ∈ S) (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S \ Z, _root_.Nat.card {𝔓 // 𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓 ∈ T ∧
      𝔓.asIdeal.inertiaDeg (𝓞 K) = 1} = c) {δ : ℝ} :
    T.HasDirichletDensity δ ↔ S.HasDirichletDensity (δ / c) := by
  -- The primes of `T` of residue degree above one over `K` have residue degree above one over
  -- `ℚ`, so they are negligible.
  set T₁ : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 E)) := {𝔓 | 𝔓 ∈ T ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1}
  have hT : (T₁ ∆ T).HasDirichletDensity 0 := by
    refine TauCeti.hasDirichletDensity_higherDegreePrimes.zero_of_subset fun 𝔓 h𝔓 ↦ ?_
    simp only [T₁, _root_.Set.mem_symmDiff, _root_.Set.mem_ofPred_eq] at h𝔓
    have hpos := _root_.Ideal.inertiaDeg_pos 𝔓.asIdeal (𝓞 K)
    have hne : 𝔓.asIdeal.inertiaDeg (𝓞 K) ≠ 1 := by tauto
    exact _root_.TauCeti.mem_higherDegreePrimes_of_one_lt_inertiaDeg (K := K) (by omega)
  rw [← _root_.NumberField.Set.hasDirichletDensity_iff_of_symmDiff hT]
  have hnorm (𝔓 : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (h𝔓 : 𝔓 ∈ T₁) :
      _root_.Ideal.absNorm 𝔓.asIdeal = _root_.Ideal.absNorm (𝔓.under (𝓞 K)).asIdeal := by
    have : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 K)).asIdeal :=
      ⟨_root_.IsDedekindDomain.HeightOneSpectrum.under_asIdeal _ 𝔓⟩
    rw [← _root_.Ideal.absNorm_pow_inertiaDeg (𝔓.under (𝓞 K)).asIdeal 𝔓.asIdeal, h𝔓.2, _root_.pow_one]
  refine _root_.NumberField.Set.hasDirichletDensity_iff_of_card_fiber_of_negligible hZ
    (fun 𝔓 h𝔓 ↦ ⟨hmaps 𝔓 h𝔓.1.1 h𝔓.1.2 h𝔓.2, h𝔓.2⟩)
    (fun 𝔓 h𝔓 ↦ hnorm 𝔓 h𝔓.1) (fun 𝔓 h𝔓 ↦ (hnorm 𝔓 h𝔓.1).ge) hc hfiber
    (m := _root_.Module.finrank K E) fun 𝔭 _ ↦
      (_root_.Set.encard_le_encard _root_.Set.inter_subset_right).trans
        (𝔭.encard_setOf_under_eq_le_finrank (E := E))

end NumberField.Set

end
end
