-- Prove2me | solution 1 for NumberField.Set.HasDirichletDensity.of_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:48:28.718051+00:00
-- url     : https://prove2.me/submissions/9f0fcdbf-0d21-4ca5-8ddc-fb854520dc7f

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
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
import Theorems.Thm_NumberField_Set_primeIdealZetaSum_le_add_symmDiff
import Theorems.Thm_TauCeti_LSeriesSummable_normCoeff_one_iff
import Theorems.Thm_TauCeti_summable_idealTerm_of_norm_normCoeff_eq_sum_norm

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











-- The proof below follows `NumberField.Set.HasDirichletDensity.le_one` from
-- `Mathlib.NumberTheory.NumberField.DirichletDensity`.




























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
end NumberField.Set
section NumberField.Set
open NumberField NumberField.Set

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.NumberField _root_.TauCeti.NumberField _root_.symmDiff _root_.Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}











/-- **Sets of density zero are negligible.** If `T` has Dirichlet density `δ` and the symmetric
difference `S ∆ T` has Dirichlet density zero, then `S` has Dirichlet density `δ`. -/
theorem solution (hT : T.HasDirichletDensity δ)
    (h : (S ∆ T).HasDirichletDensity 0) : S.HasDirichletDensity δ := by
  have hT' := _root_.NumberField.Set.hasDirichletDensity_iff.1 hT
  have h' := _root_.NumberField.Set.hasDirichletDensity_iff.1 h
  have hlo : _root_.Filter.Tendsto (fun s ↦ (T.primeIdealZetaSum s - (S ∆ T).primeIdealZetaSum s) /
      (_root_.Set.univ : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s) (𝓝[>] 1) (𝓝 δ) := by
    simpa only [_root_.sub_div, _root_.sub_zero] using hT'.sub h'
  have hhi : _root_.Filter.Tendsto (fun s ↦ (T.primeIdealZetaSum s + (S ∆ T).primeIdealZetaSum s) /
      (_root_.Set.univ : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s) (𝓝[>] 1) (𝓝 δ) := by
    simpa only [_root_.add_div, _root_.add_zero] using hT'.add h'
  refine _root_.NumberField.Set.hasDirichletDensity_iff.2 <| _root_.tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [_root_.self_mem_nhdsWithin] with s (hs : 1 < s)
    -- `P_T ≤ P_S + P_{S ∆ T}`, since `T ∆ S = S ∆ T`.
    have := _root_.NumberField.Set.primeIdealZetaSum_le_add_symmDiff (S := T) (T := S)
      (_root_.TauCeti.summable_absNorm_rpow_subtype_of_one_lt S hs)
      (_root_.TauCeti.summable_absNorm_rpow_subtype_of_one_lt _ hs)
    rw [_root_.symmDiff_comm] at this
    exact _root_.div_le_div_of_nonneg_right (by linarith) (Set.univ.primeIdealZetaSum_nonneg s)
  · filter_upwards [_root_.self_mem_nhdsWithin] with s (hs : 1 < s)
    exact _root_.div_le_div_of_nonneg_right (_root_.NumberField.Set.primeIdealZetaSum_le_add_symmDiff
      (_root_.TauCeti.summable_absNorm_rpow_subtype_of_one_lt T hs)
      (_root_.TauCeti.summable_absNorm_rpow_subtype_of_one_lt _ hs)) (Set.univ.primeIdealZetaSum_nonneg s)









end NumberField.Set

open _root_.IsDedekindDomain _root_.NumberField _root_.NumberField.Set

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {K : Type*} [Field K] [NumberField K]







end TauCeti

end
end
