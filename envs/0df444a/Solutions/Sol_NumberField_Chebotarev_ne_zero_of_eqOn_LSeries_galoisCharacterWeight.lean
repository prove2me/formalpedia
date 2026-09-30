-- Prove2me | solution 1 for NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:11:55.859981+00:00
-- url     : https://prove2.me/submissions/47c2c19a-a5ac-435a-91b7-0a311bc27bda

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Trivial
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_LSeriesSummable_normCoeff_one_iff
import Theorems.Thm_TauCeti_LSeries_ne_zero_of_threeFourOne
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_LSeries_restrict
import Theorems.Thm_TauCeti_UnitaryIdealWeight_norm_LSeries_threeFourOne_ge_one
import Theorems.Thm_TauCeti_summable_idealTerm_of_norm_normCoeff_eq_sum_norm

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Growth `O((σ - 1)⁻¹)` from a one-sided limit of `(σ - 1) f(σ)`

If `(σ - 1) f(σ)` has a limit as the real variable `σ` tends to `1` from the right, then
`f(σ) = O((σ - 1)⁻¹)` there. This is how a bound of this shape is usually obtained for a
Dedekind zeta function or an `L`-series near `s = 1`, from the limit of `(s - 1) L(s)` along the
real axis.

## Main results

* `TauCeti.isBigO_inv_sub_one_of_tendsto_sub_one_mul`: if `(σ - 1) f(σ)` converges as `σ → 1⁺`,
  then `f(σ) = O((σ - 1)⁻¹)` as `σ → 1⁺`.

## References

* Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David
  Loeffler, derives the same bound for the Dirichlet `L`-function of the trivial character in
  `DirichletCharacter.LFunctionTrivChar_isBigO_near_one_horizontal`.
-/

 section

open Asymptotics Complex Filter
open scoped Topology

namespace TauCeti

/-- If `(σ - 1) f(σ)` has a limit as `σ → 1⁺` through real values, then `f(σ) = O((σ - 1)⁻¹)`
as `σ → 1⁺`. -/
theorem isBigO_inv_sub_one_of_tendsto_sub_one_mul {f : ℝ → ℂ} {r : ℂ}
    (h : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - 1) * f σ) (𝓝[>] 1) (𝓝 r)) :
    f =O[𝓝[>] 1] fun σ : ℝ ↦ (σ - 1)⁻¹ := by
  have hinv : (fun σ : ℝ ↦ ((σ : ℂ) - 1)⁻¹) =O[𝓝[>] 1] fun σ : ℝ ↦ (σ - 1)⁻¹ :=
    isBigO_of_le _ fun σ ↦ by rw [← ofReal_one, ← ofReal_sub, ← ofReal_inv, norm_real]
  refine ((h.isBigO_one ℝ).mul hinv).congr' ?_ (by simp)
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have : (σ : ℂ) - 1 ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero]
    exact sub_ne_zero.mpr hσ.ne'
  field_simp

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
# Completely multiplicative ideal weights

The completely multiplicative specializations of `TauCeti.IdealArithmeticFunction`: the two
carriers on which every Euler product, Hecke character and character-family argument of this
development is stated.

A `TauCeti.MultiplicativeIdealWeight K` is a monoid-with-zero homomorphism
`Ideal (𝓞 K) →*₀ ℂ` killing only finitely many height-one primes, and
`TauCeti.UnitaryIdealWeight K` is the subtype of those whose values have modulus `1` away from
that finite bad set. Using Mathlib's `→*₀` vocabulary is what pins the zero-ideal law
`χ ⊥ = 0`; the finiteness condition is what bounds the bad local factors of the Euler product.

Both carriers are *degree one*: the value at `𝔭 ^ n` is forced to be `χ 𝔭 ^ n`. They are
therefore deliberately too narrow for the ideal Möbius function or for coefficient systems
whose prime-power values are independent local data; those get separate carriers.

The organising notion is `Ideal.IsPrimeTo`, an ideal of a Dedekind domain being nonzero and
divisible by no prime of a given set; it is stated for a general Dedekind domain because
nothing in it is specific to a number field. The good ideals of a weight are the ideals
prime to its bad primes, and `Ideal.IsPrimeTo.induction_on` factors such an ideal into
good primes; this is the engine behind both
`TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood` and
`TauCeti.UnitaryIdealWeight.norm_eq_one`.

## Main declarations

* `Ideal.IsPrimeTo`: an ideal is nonzero and no prime of `S` divides it, with its
  multiplicativity (`Ideal.isPrimeTo_mul_iff`) and its induction principle
  (`Ideal.IsPrimeTo.induction_on`);
* `TauCeti.MultiplicativeIdealWeight`: the general completely multiplicative carrier, its
  `TauCeti.MultiplicativeIdealWeight.badPrimes` and its good ideals
  (`TauCeti.MultiplicativeIdealWeight.IsGood`);
* `TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood`: a weight is nonzero exactly on
  the good ideals;
* `TauCeti.MultiplicativeIdealWeight.ext_heightOneSpectrum`: a weight is determined by its
  values at the height-one primes;
* `TauCeti.MultiplicativeIdealWeight.ofBadPrimes`, the pointwise `CommMonoid` structure (whose
  unit is the trivial weight), `TauCeti.MultiplicativeIdealWeight.restrict`,
  `TauCeti.MultiplicativeIdealWeight.conj` and
  `TauCeti.MultiplicativeIdealWeight.normTwist`: the constructors and operations;
* `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood` and
  `TauCeti.MultiplicativeIdealWeight.IsTrivialOnGood`: the weights agreeing with a purely
  imaginary norm twist, respectively with the trivial weight, on their good ideals, with the
  structure theorem `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.eq_normTwist`, its
  converse `TauCeti.MultiplicativeIdealWeight.isNormTwistOnGood_normTwist_ofBadPrimes`, and the
  behaviour of the parameter under conjugation, the pointwise product and a further twist;
* `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction`: passage to the general
  carrier, inverted by `TauCeti.IdealArithmeticFunction.zeroExtend`;
* `TauCeti.UnitaryIdealWeight`: the unitary subtype, with
  `TauCeti.UnitaryIdealWeight.norm_eq_one` on all good ideals,
  `TauCeti.UnitaryIdealWeight.norm_normTwist` for the modulus of an arbitrary norm twist,
  `TauCeti.UnitaryIdealWeight.ofPowEqOne` for finite-order weights, and the operations
  `TauCeti.UnitaryIdealWeight.conj`, `TauCeti.UnitaryIdealWeight.restrict` and
  `TauCeti.UnitaryIdealWeight.normTwist` (the last for the imaginary norm twists only), and
  `TauCeti.UnitaryIdealWeight.toIdealArithmeticFunction` for its passage to the general carrier;
* `TauCeti.MultiplicativeIdealWeight.map` and `TauCeti.UnitaryIdealWeight.map`, with their
  equivalences `mapEquiv`: functoriality under an isomorphism `K ≃+* L` of the ambient fields,
  together with the identity and composition laws, the preservation of the pointwise product
  (`map_one` and `map_mul` on both carriers), the naturality of restriction, conjugation and norm
  twists, and the compatibilities
  `TauCeti.MultiplicativeIdealWeight.badPrimes_map` and
  `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_map`.

## Rejection tests

The two worked negative examples of this layer are proved here.
`TauCeti.MultiplicativeIdealWeight.coe_ne_const_one` says the everywhere-one function on *all*
integral ideals underlies no weight, because `→*₀` forces the value `0` at `⊥` — the
everywhere-one function on the *nonzero* ideals is the trivial weight instead
(`TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one`).
`TauCeti.UnitaryIdealWeight.norm_normTwist_apply_ne_one` says that a norm twist with
`Re z ≠ 0` changes the modulus at every good ideal of absolute norm greater than one, so such
twists live only in the general carrier.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* `TauCetiRoadmap/ArithmeticDirichletSeries/README.md` and its `Suggested.lean` target
  signatures: this file implements the Layer 0 export contract stated there, and follows its
  naming and organization for the two weight carriers.
-/

 section

namespace TauCeti

open _root_.NumberField _root_.IsDedekindDomain _root_.nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]



/-!
### The general carrier of completely multiplicative ideal weights
-/



namespace MultiplicativeIdealWeight













/-- A multiplicative ideal weight is determined by its values at the height-one primes: every
nonzero ideal of `𝓞 K` is a product of them. -/
theorem ext_heightOneSpectrum {χ ψ : MultiplicativeIdealWeight K}
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), χ 𝔭.asIdeal = ψ 𝔭.asIdeal) : χ = ψ := by
  ext I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => rw [map_zero, map_zero]
  | h₂ x hx => rw [Ideal.isUnit_iff.mp hx, apply_top, apply_top]
  | h₃ a p _ hp ih =>
    rw [_root_.map_mul, _root_.map_mul, ih, h ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩]







variable {χ : MultiplicativeIdealWeight K}







/-!
### Constructors and operations
-/

section Operations

variable {S : Set (HeightOneSpectrum (𝓞 K))}







@[simp]
theorem isGood_ofBadPrimes_iff (hS : S.Finite) {I : Ideal (𝓞 K)} :
    (ofBadPrimes S hS).IsGood I ↔ Ideal.IsPrimeTo I S := by
  simp only [IsGood, badPrimes_ofBadPrimes]





























/-- Restricting the trivial weight away from `S` gives the indicator weight of ideals prime to
every prime in `S`. -/
@[simp]
theorem one_restrict (hS : S.Finite) :
    (1 : MultiplicativeIdealWeight K).restrict S hS = ofBadPrimes S hS :=
  one_mul _



















/-!
### Weights that are norm twists on their good locus
-/













/-- The indicator of the ideals prime to a finite set `S` of primes is trivial on its good
ideals, which are exactly those ideals. -/
theorem isTrivialOnGood_ofBadPrimes (hS : S.Finite) : (ofBadPrimes S hS).IsTrivialOnGood := by
  classical
  intro I hI
  rw [ofBadPrimes_apply]
  simp [(isGood_ofBadPrimes_iff hS).mp hI]











end Operations

/-!
### Passage to the general carrier, and the zero-ideal rejection test
-/













@[simp]
theorem toIdealArithmeticFunction_one :
    (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction = 1 := by
  ext I
  have hI : (I : Ideal (𝓞 K)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  simp [one_apply, hI]

@[simp]
theorem toIdealArithmeticFunction_mul (χ ψ : MultiplicativeIdealWeight K) :
    (χ * ψ).toIdealArithmeticFunction =
      χ.toIdealArithmeticFunction * ψ.toIdealArithmeticFunction := by
  ext I
  simp



/-!
### Functoriality under an isomorphism of fields
-/

section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]





















/-! Transport preserves the pointwise `CommMonoid` structure. -/













end Transport

end MultiplicativeIdealWeight

/-!
### The unitary subtype
-/



namespace UnitaryIdealWeight



-- Source. The statement and its proof follow `DirichletCharacter.norm_le_one` in Mathlib's
-- `Mathlib/NumberTheory/DirichletCharacter/Bounds.lean`, transposed from a Dirichlet character on
-- `ZMod n` to a unitary ideal weight: the case split there is on `IsUnit a` and closes with
-- `map_nonunit`, here it is on `MultiplicativeIdealWeight.IsGood` and closes with
-- `apply_eq_zero_iff_not_isGood`.

















@[simp]
theorem val_ofPowEqOne (χ : MultiplicativeIdealWeight K) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → χ 𝔭.asIdeal ^ n = 1) :
    (ofPowEqOne χ hn h).1 = χ := (rfl)























section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]















/-! Transport preserves the pointwise `CommMonoid` structure of the unitary carrier too. -/











end Transport



@[simp]
theorem toIdealArithmeticFunction_apply (χ : UnitaryIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ.1 I := (rfl)

/-- The ideal arithmetic function of a unitary weight agrees with that of its underlying
multiplicative weight. -/
theorem toIdealArithmeticFunction_eq_val (χ : UnitaryIdealWeight K) :
    χ.toIdealArithmeticFunction = χ.1.toIdealArithmeticFunction := by
  funext I
  rw [toIdealArithmeticFunction_apply,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]











end UnitaryIdealWeight

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
# The trivial ideal weight and Dedekind zeta coefficients

This file identifies the norm coefficients of the trivial ideal weight with the coefficients of
the Dedekind zeta function.  There is one necessary exception: Mathlib's coefficient counts all
integral ideals and therefore has value `1` at index zero, contributed by the zero ideal, whereas
an `ArithmeticFunction` has value zero there.  Since `LSeries` ignores its zero coefficient, the
two coefficient systems define the same series.

For the rational field the ring of integers is isomorphic to `ℤ`.  Mapping an ideal through this
isomorphism and using `Int.ideal_span_absNorm_eq_self` shows that there is exactly one ideal of
each positive norm.  Thus the trivial ideal weight over `ℚ` regroups to the constant coefficient
`1` at every positive index, as for the Riemann zeta function.

## Roadmap role

This is Layer **1.3**, the trivial specialization, of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  It completes Layer 1 without asserting the
exact abscissa of convergence; that is Layer 5, proved in
`TauCeti.abscissaOfAbsConv_normCoeff_one`.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField

variable (K : Type*) [Field K] [NumberField K]





/-- The Dedekind zeta function is the `LSeries` of `dedekindZetaCoeff`. -/
theorem dedekindZeta_eq_LSeries_dedekindZetaCoeff (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (fun n ↦ (dedekindZetaCoeff K n : ℂ)) s := by
  simp [NumberField.dedekindZeta, dedekindZetaCoeff]

private def normFiberSubtypeEquiv {n : ℕ} (hn : n ≠ 0) :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n} where
  toFun I := ⟨I.1, I.2⟩
  invFun I :=
    ⟨⟨I.1, by
      rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
      exact fun hzero ↦ hn (I.2.symm.trans hzero)⟩, I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Away from zero, the cardinality of the finite nonzero-ideal norm fibre is the corresponding
Dedekind zeta coefficient. -/
theorem card_normFiber_eq_dedekindZetaCoeff {n : ℕ} (hn : n ≠ 0) :
    (normFiber K n).card = dedekindZetaCoeff K n := by
  rw [← Nat.card_eq_finsetCard, dedekindZetaCoeff]
  exact Nat.card_congr <|
    (Equiv.subtypeEquivRight fun I ↦ mem_normFiber (K := K)).trans
      (normFiberSubtypeEquiv K hn)

/-- The trivial ideal arithmetic function regroups to the Dedekind zeta coefficients away from
zero.  At zero its norm coefficient is forced to vanish by the `ArithmeticFunction` carrier. -/
@[simp]
theorem normCoeff_one_apply (n : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) n =
      if n = 0 then 0 else dedekindZetaCoeff K n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, normCoeff_eq_sum_normFiber]
    simp [card_normFiber_eq_dedekindZetaCoeff K hn]



/-- Regrouping the trivial ideal weight gives Mathlib's Dedekind zeta function. -/
theorem dedekindZeta_eq_LSeries_normCoeff_one (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (normCoeff K (1 : IdealArithmeticFunction K)) s := by
  rw [dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  apply LSeries_congr
  intro n hn
  rw [normCoeff_one_apply, if_neg hn]













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
namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The analytic Euler product of an ideal arithmetic function

`TauCeti.EulerProductData.normCoeff_eq_eulerProduct` identifies the norm coefficients of bundled
Euler-product data with a formal Euler product, coefficient by coefficient. This file supplies the
analytic statement it does not: where the Dirichlet series indexed by the nonzero ideals converges
absolutely, the infinite product of the local Euler factors converges, in the unrestricted sense
of `HasProd` over the height-one primes, to the `LSeries` of the norm coefficients.

The local factor at a height-one prime `P` is the `LSeries` of the canonical local arithmetic
factor, equivalently the prime-power Dirichlet series `∑' e, f (P ^ e) / N(P ^ e) ^ s`. For a
completely multiplicative weight that series is geometric, and the factor takes the familiar
closed form `(1 - χ(P) N(P) ^ (-s))⁻¹`; specializing to the trivial weight gives the Euler
product of the Dedekind zeta function.

## Main definitions

* `TauCeti.EulerProductData.eulerFactor`: the local Euler factor at a height-one prime.

## Main results

* `TauCeti.EulerProductData.hasProd_eulerFactor`: the **analytic Euler product**, when the
  ideal-indexed Dirichlet series converges absolutely at `s`.
* `TauCeti.EulerProductData.norm_absNorm_cpow_neg_le_radius_localPowerSeries`: a lower bound for
  the convergence radius of a local power series from absolute convergence at a real point.
* `TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor`: the same product, with the local factors
  in the closed geometric form available for a completely multiplicative weight.
* `TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm`: the `L`-series is
  **nonzero** wherever the ideal-indexed series converges absolutely.
* `TauCeti.dedekindZeta_eulerProduct_hasProd`: the **Euler product of the Dedekind zeta
  function**, valid on `Re s > 1`.
* `TauCeti.dedekindZeta_ne_zero_of_one_lt_re`: the Dedekind zeta function is **nonzero** on
  `Re s > 1`.
* `IsDedekindDomain.HeightOneSpectrum.one_lt_norm_absNorm_cpow` and
  `IsDedekindDomain.HeightOneSpectrum.absNorm_cpow_sub_one_ne_zero`: analytic bounds for the
  complex powers of prime-ideal norms on the right half-plane.
* `IsDedekindDomain.HeightOneSpectrum.logDeriv_one_sub_absNorm_cpow_neg`: the logarithmic
  derivative of a deleted Euler factor.

The nonvanishing is pointwise, at each `s` where the ideal-indexed series converges absolutely, and
nothing is claimed off that region. It is not a formality: an unconditionally convergent product of
nonzero factors may still vanish.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `EulerProduct` API, whose `Nat.Primes`-indexed statements this file mirrors for the
  height-one primes of a number field.
-/

 section

open scoped _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm of a height-one prime, cast to `ℂ`, is nonzero. -/
theorem natCast_absNorm_ne_zero (P : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (NumberField.HeightOneSpectrum.one_lt_absNorm P).ne_bot









end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.ComplexOrder

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}

/-! ### The local Euler factor -/







end EulerProductData

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {s : ℂ}

/-! ### Restriction to a set of primes, analytically -/















end IdealArithmeticFunction

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}













/-! ### The infinite Euler product -/







end EulerProductData

/-! ### Completely multiplicative weights -/

namespace MultiplicativeIdealWeight

open _root_.TauCeti.IdealArithmeticFunction

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}















end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function -/







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
# Deleting finitely many Euler factors

Restricting Euler-product data away from a finite set `S` of primes, keeping only the
coefficients of the ideals prime to `S`, replaces the local Euler factors at `S` by `1` and leaves
the others untouched. On the half-plane of absolute convergence the two `L`-series therefore
differ by the finitely many deleted factors; for a completely multiplicative weight `χ` the
restriction `χ.restrict S` divides the `L`-series by `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))⁻¹`.

For the trivial weight the restriction is `ofBadPrimes S`, the indicator of the ideals prime to
`S`, and its `L`-series is the Dedekind zeta function with the Euler factors at `S` removed:

`L_S(s) = ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`  for `Re s > 1`.

The correction factor does not vanish on `Re s > 0`, because
`|N(𝔭) ^ s| = N(𝔭) ^ (Re s) > 1` there. As `s → 1⁺`, the normalized expression
`(s - 1) L_S(s)` tends to `dedekindZeta_residue K` multiplied by the nonzero number
`∏ 𝔭 ∈ S, (1 - N(𝔭)⁻¹)`. The logarithmic derivative of `L_S` differs from that of `ζ_K` by the
finite sum `∑ 𝔭 ∈ S, log N(𝔭) / (N(𝔭) ^ s - 1)`, which is holomorphic on `Re s > 0` and in
particular across the line `Re s = 1`. This is the form in which Dirichlet series whose Euler
products omit the ramified primes, such as the trivial Galois-character series, are compared with
`ζ_K`.

## Main results

* `TauCeti.EulerProductData.eulerFactor_restrictAway_of_mem`,
  `TauCeti.EulerProductData.eulerFactor_restrictAway_of_notMem`: restricting away from `S`
  replaces the local factors at `S` by `1` and keeps the others.
* `TauCeti.EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor`: multiplying the `L`-series
  of the restriction by the deleted local factors recovers the original `L`-series.
* `TauCeti.MultiplicativeIdealWeight.LSeries_restrict`: the same for a completely multiplicative
  weight, with the deleted factors in closed form.
* `TauCeti.LSeries_ofBadPrimes`: the `L`-series of the indicator of the ideals prime to `S` is
  `ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))` on `Re s > 1`.
* `TauCeti.prod_one_sub_absNorm_cpow_neg_ne_zero`: the correction factor has no zero on
  `Re s > 0`.
* `TauCeti.dedekindZeta_residue_mul_prod_one_sub_absNorm_cpow_neg_one_ne_zero`: the corrected
  residue at `s = 1` is nonzero.
* `TauCeti.tendsto_sub_one_mul_LSeries_ofBadPrimes`: the normalized right-hand limit at `s = 1`.
* `TauCeti.logDeriv_LSeries_ofBadPrimes`: the logarithmic derivative on `Re s > 1`, and
  `TauCeti.differentiableOn_sum_log_absNorm_div_cpow_sub_one`: the correction term in it is
  holomorphic on `Re s > 0`.
* `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.LSeries_normCoeff` and
  `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.tendsto_sub_one_mul_LSeries`: a weight that
  is a norm twist with parameter `u` on its good ideals has for `L`-series such a deleted zeta
  function read at `s - u * I`, with the corresponding pole at `s = 1 + u * I`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField _root_.Topology
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

variable (D : EulerProductData K) {s : ℂ}









end EulerProductData

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}



end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function with finitely many Euler factors deleted -/





/-- **The Dedekind zeta function with the Euler factors at `S` deleted.** For a finite set `S` of
primes and `Re s > 1`, the `L`-series of the indicator of the ideals prime to `S` is
`ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`. -/
theorem LSeries_ofBadPrimes (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
        S.finite_toSet).toIdealArithmeticFunction) s =
      NumberField.dedekindZeta K s * ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) := by
  have hsum : Summable
      (idealTerm K (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction s) := by
    rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact summable_idealTerm_one_iff.mpr hs
  rw [← MultiplicativeIdealWeight.one_restrict, MultiplicativeIdealWeight.LSeries_restrict _ S hsum,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
    ← dedekindZeta_eq_LSeries_normCoeff_one]
  congr 1
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  rw [MultiplicativeIdealWeight.one_apply, if_neg P.ne_bot, Complex.cpow_neg, one_div]

/-- **The normalized right-hand limit at `s = 1` after deleting Euler factors.** As `s → 1⁺`,
`(s - 1) L_S(s)` tends to `dedekindZeta_residue K` multiplied by
`∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-1))`, which is nonzero by
`prod_one_sub_absNorm_cpow_neg_ne_zero`. -/
theorem tendsto_sub_one_mul_LSeries_ofBadPrimes (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (normCoeff K
        (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
          S.finite_toSet).toIdealArithmeticFunction) s) (𝓝[>] 1)
      (𝓝 (NumberField.dedekindZeta_residue K *
        ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ)))) := by
  have hcont : Continuous fun s : ℝ ↦ ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-(s : ℂ))) :=
    continuous_finsetProd _ fun P _ ↦ continuous_const.sub <|
      (Complex.continuous_ofReal.neg).const_cpow <| Or.inl P.natCast_absNorm_ne_zero
  have hprod := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  rw [Complex.ofReal_one] at hprod
  refine ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).mul hprod).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  rw [LSeries_ofBadPrimes S (by simpa using hs), mul_assoc]





/-! ### Weights that are norm twists on their good ideals -/

namespace MultiplicativeIdealWeight





end MultiplicativeIdealWeight

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
# The ideal weight of a Galois character

For a finite Galois extension `L / K` of number fields and a character `χ : Gal(L/K) →* ℂˣ`, this
file builds the *canonical ideal weight* `galoisCharacterWeight χ`: the completely multiplicative
function on the ideals of `𝓞 K` whose value at a height-one prime `𝔭` is `χ (Frob 𝔭)` when `𝔭` is
unramified in `L`, and `0` when `𝔭` ramifies. Since `Gal(L/K)` is finite those unramified values
are roots of unity, so the same weight is packaged a second time as a
`TauCeti.UnitaryIdealWeight K`.

Nothing here assumes that `L / K` is cyclotomic: the construction needs only `[IsGalois K L]`, and
the character is an arbitrary degree-one complex character of the Galois group. The Dirichlet
weight is the specialisation `L / K = ℚ(ζ_m) / ℚ`, where the cyclotomic character identifies
`Gal(ℚ(ζ_m)/ℚ)` with `(ZMod m)ˣ` and `χ` is a Dirichlet character mod `m`. Over a general base `K`
that character is still injective but need not be surjective: restriction identifies
`Gal(K(ζ_m)/K)` with the subgroup of `(ZMod m)ˣ` fixing `K ∩ ℚ(ζ_m)`, and that subgroup is all of
`(ZMod m)ˣ` exactly when `K ∩ ℚ(ζ_m) = ℚ`. The declarations are named for the generality they
actually have.

The weight is **total**, and that is a design constraint rather than a convenience: a weight
specified only away from ramification leaves its values at the bad primes unconstrained, so the
Euler product and the orthogonality identities would not pin it down. Vanishing at the ramified
primes is what makes the ramified Euler factors drop out as `(1 - 0)⁻¹ = 1`.

## Main definitions

* `MonoidHom.galoisCharacterWeight`: the weight of `χ`, packaged as a
  `TauCeti.MultiplicativeIdealWeight K`.
* `MonoidHom.galoisCharacterUnitaryWeight`: the same weight packaged as a
  `TauCeti.UnitaryIdealWeight K`, its values having modulus `1` away from the ramified primes.

## Main results

* `MonoidHom.galoisCharacterWeight_apply_of_unramified`: at an unramified height-one prime the
  weight is `χ` of the Artin symbol.
* `MonoidHom.galoisCharacterWeight_apply_eq_zero_iff`: the weight vanishes at a height-one prime
  exactly when that prime ramifies in `L`.
* `MonoidHom.badPrimes_galoisCharacterWeight`: the bad primes of the weight are exactly the
  ramified primes.
* `MonoidHom.galoisCharacterWeight_one`: the weight of the trivial character is the indicator of
  the ideals prime to the ramified primes, so its `L`-series is the Dedekind zeta function with the
  ramified Euler factors deleted.
* `MonoidHom.galoisCharacterWeight_mul`: the weight of a product of characters is the product of
  their weights.
* `MonoidHom.val_galoisCharacterUnitaryWeight`: the unitary packaging has the same underlying
  weight.
* `MonoidHom.norm_galoisCharacterWeight_le_one`: the weight of a Galois character is bounded by
  `1`.
* `MonoidHom.summable_idealTerm_galoisCharacterWeight`: the ideal series of a Galois character
  converges absolutely on `Re s > 1`.

## Implementation notes

The weight is packaged as a `TauCeti.MultiplicativeIdealWeight K` rather than as a bare function
`Ideal (𝓞 K) → ℂ`, so that the totality above is expressed in the carrier's own `badPrimes` API:
the bad primes of `χ.galoisCharacterWeight` are exactly `ramifiedPrimes K L`.

`TauCeti.UnitaryIdealWeight K` is the subtype of those multiplicative weights whose values have
modulus `1` away from the bad primes, so the unitary packaging records strictly more than the
multiplicative one and is not a replacement for it: `galoisCharacterWeight` remains the definition
everything else is stated about, and `val_galoisCharacterUnitaryWeight` is the bridge. Unitarity is
a property of the weight rather than of `χ`, so no hypothesis constrains `χ` itself to the unit
circle.

## References

Adapted from `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_mul` and
`norm_galoisCharacterOnIdeal_le_one` in `CebotarevDensity/ZetaProduct.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, following Sharifi,
*Algebraic Number Theory*, Notation 7.1.17. The factorization-product definition and the
`Multiset.map_add`/`Multiset.prod_add` multiplicativity argument are the source's; the
`MultiplicativeIdealWeight` packaging and the `artinSymbol` totalization are not the source's and
are new here. The source likewise names the construction for a general Galois character.
-/

 section

open scoped _root_.NumberField

open _root_.IsDedekindDomain (HeightOneSpectrum)

open _root_.UniqueFactorizationMonoid
open _root_.TauCeti

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

















end NumberField.Chebotarev

open _root_.NumberField _root_.NumberField.Chebotarev

namespace MonoidHom

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]











/-- **The weight of the trivial character** is the indicator of the ideals prime to the ramified
primes. Its `L`-series is therefore the Dedekind zeta function of `K` with the Euler factors at the
ramified primes deleted (`TauCeti.LSeries_ofBadPrimes`). -/
@[simp]
theorem galoisCharacterWeight_one :
    galoisCharacterWeight (L := L) (1 : (L ≃ₐ[K] L) →* ℂˣ) =
      TauCeti.MultiplicativeIdealWeight.ofBadPrimes (ramifiedPrimes K L : Set _)
        (ramifiedPrimes K L).finite_toSet := by
  classical
  refine TauCeti.MultiplicativeIdealWeight.ext_heightOneSpectrum fun 𝔭 ↦ ?_
  rw [TauCeti.MultiplicativeIdealWeight.ofBadPrimes_apply, Ideal.isPrimeTo_asIdeal_iff,
    Finset.mem_coe]
  by_cases h : 𝔭 ∈ ramifiedPrimes K L
  · simp only [h, not_true_eq_false, ↓reduceIte]
    exact (galoisCharacterWeight_apply_eq_zero_iff _ 𝔭).mpr h
  · simp only [h, not_false_eq_true, ↓reduceIte]
    rw [galoisCharacterWeight_apply_of_unramified _ 𝔭
        (not_not.mp (mt (mem_ramifiedPrimes_iff 𝔭).mpr h)), MonoidHom.one_apply, Units.val_one]

/-- **The weight of a product of characters is the product of their weights.** Both sides vanish
at the ramified primes and agree with `χ ψ` of the Artin symbol at the others. The weight of the
trivial character is not the trivial weight (`galoisCharacterWeight_one`), so this is
multiplicativity without a unit. -/
@[simp]
theorem galoisCharacterWeight_mul (χ ψ : (L ≃ₐ[K] L) →* ℂˣ) :
    galoisCharacterWeight (L := L) (χ * ψ) =
      galoisCharacterWeight (L := L) χ * galoisCharacterWeight (L := L) ψ := by
  refine TauCeti.MultiplicativeIdealWeight.ext_heightOneSpectrum fun 𝔭 ↦ ?_
  rw [TauCeti.MultiplicativeIdealWeight.mul_apply]
  by_cases h : 𝔭 ∈ ramifiedPrimes K L
  · simp only [(galoisCharacterWeight_apply_eq_zero_iff _ 𝔭).mpr h, mul_zero]
  · have hur := not_not.mp (mt (mem_ramifiedPrimes_iff 𝔭).mpr h)
    rw [galoisCharacterWeight_apply_of_unramified _ 𝔭 hur,
      galoisCharacterWeight_apply_of_unramified _ 𝔭 hur,
      galoisCharacterWeight_apply_of_unramified _ 𝔭 hur, MonoidHom.mul_apply, Units.val_mul]



/-- The unitary packaging has the same underlying weight. -/
@[simp]
theorem val_galoisCharacterUnitaryWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    (galoisCharacterUnitaryWeight (L := L) χ).1 = galoisCharacterWeight (L := L) χ := by
  simp [galoisCharacterUnitaryWeight]





end MonoidHom

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
# The 3-4-1 bound for Galois character series

The Euler products of a Galois character, its square, and the trivial character satisfy the
classical 3-4-1 positivity inequality on `Re s > 1`. All three products omit exactly the primes
ramified in the extension. This lower bound is the positivity input for proving nonvanishing of
the continued character series on the line `Re s = 1`.

It is the specialization of `TauCeti.UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one` to the
unitary weight of a Galois character, measured against the weight of the trivial character: that
weight is trivial on its good ideals, and its bad primes, the ramified ones, are those of every
character weight.
-/

 section

namespace NumberField.Chebotarev

open Complex TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The 3-4-1 bound for Galois character Euler products.** For `σ > 1`, the product of the
trivial-character series to the third power, the `χ`-series at `σ + it` to the fourth power, and
the `χ²`-series at `σ + 2it` has norm at least one. The Euler factors at ramified primes are
omitted in all three series. -/
theorem norm_galoisCharacterLSeries_threeFourOne_ge_one
    (χ : (L ≃ₐ[K] L) →* ℂˣ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖LSeries (normCoeff K
        (1 : (L ≃ₐ[K] L) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction) σ ^ 3 *
      LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction)
        ((σ : ℂ) + I * t) ^ 4 *
      LSeries (normCoeff K (χ ^ 2).galoisCharacterWeight.toIdealArithmeticFunction)
        ((σ : ℂ) + 2 * I * t)‖ := by
  have h₀ : (MonoidHom.galoisCharacterWeight (K := K) (L := L) 1).IsTrivialOnGood := by
    simpa using MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes _
  have h := UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one
    (MonoidHom.galoisCharacterUnitaryWeight (L := L) χ) h₀ (by simp) hσ t
  simpa [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, pow_two] using h

end NumberField.Chebotarev

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
# Nonvanishing of Galois character series on the line `Re s = 1`

Let `F / K` be a finite Galois extension of number fields and `χ` a character of `Gal(F/K)`. On
`Re s > 1` the `L`-series of `galoisCharacterWeight χ` does not vanish, by its Euler product. This
file gives criteria for a function agreeing on `Re s > 1` with the `L`-series of
`galoisCharacterWeight χ` to be nonzero at a point `s` of the line `Re s = 1`. In particular the
series of the trivial character, which is the Dedekind zeta function of `K` with the Euler factors
at the primes ramified in `F` deleted, does not vanish at any `s ≠ 1` with `Re s = 1`.

Together with the continuation across `Re s = 1`, this is what makes the logarithmic derivatives
of these series, with the pole of the trivial one subtracted, continuous on `Re s ≥ 1`: the
boundary behaviour required to apply a Tauberian theorem to the Frobenius von Mangoldt series.

## Main results

* `MonoidHom.LSeries_galoisCharacterWeight_ne_zero`: the series of `χ` is nonzero on `Re s > 1`.
* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight`: a continuation of the
  series of `χ`, differentiable at `s = 1 + it`, is nonzero at `s` provided some continuation of
  the series of `χ²` is continuous at `1 + 2it`.
* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight_of_sq_eq_one`: for
  `χ² = 1`, a continuation of the series of `χ` is nonzero on `Re s = 1` away from `s = 1`.
* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight_one`: a continuation of
  the trivial-character series is nonzero on `Re s = 1` away from `s = 1`.
* `NumberField.Chebotarev.exists_continuousOn_eq_neg_logDeriv_galoisCharacterWeight_one_sub`:
  the regularized logarithmic derivative of the trivial character extends continuously to
  `Re s ≥ 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The case analysis on `χ²` follows Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`
  (Michael Stoll and David Loeffler), where `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`
  proves the analogous statement for Dirichlet `L`-functions.
-/

 section

open _root_.Complex _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.Topology

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]



namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev



/-- **The `3-4-1` criterion for a Galois character.** Let `F / K` be a finite Galois extension,
`χ` a character of `Gal(F/K)`, and `s = 1 + it`. If `f` is complex differentiable at `s` and `f₂`
is continuous at `1 + 2it = 2s - 1`, and they agree on `Re s > 1` with the `L`-series of `χ` and of
`χ²` respectively, then `f s ≠ 0`. -/
theorem solution (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ}
    (hs : s.re = 1) {f f₂ : ℂ → ℂ} (hf : _root_.DifferentiableAt ℂ f s)
    (hfL : _root_.Set.EqOn f (_root_.LSeries (_root_.TauCeti.normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction))
      {z | 1 < z.re})
    (hf₂ : _root_.ContinuousAt f₂ (2 * s - 1))
    (hf₂L : _root_.Set.EqOn f₂
      (_root_.LSeries (_root_.TauCeti.normCoeff K (χ ^ 2).galoisCharacterWeight.toIdealArithmeticFunction))
      {z | 1 < z.re}) :
    f s ≠ 0 := by
  -- Write `s = 1 + it`, so that `2s - 1 = 1 + 2it`. The Euler-product bound
  -- `norm_galoisCharacterLSeries_threeFourOne_ge_one` and the simple pole of the trivial series
  -- at `s = 1` are the inputs of the analytic criterion `LSeries.ne_zero_of_threeFourOne`.
  have hs' : s = 1 + _root_.Complex.I * s.im := by
    conv_lhs => rw [← _root_.Complex.re_add_im s, hs, _root_.Complex.ofReal_one, _root_.mul_comm]
  have hs₂ : 2 * s - 1 = 1 + 2 * _root_.Complex.I * s.im := by
    conv_lhs => rw [hs']
    ring
  rw [hs'] at hf ⊢
  rw [hs₂] at hf₂
  refine _root_.TauCeti.LSeries.ne_zero_of_threeFourOne ?_ ?_ hf hf₂
    (f₀ := _root_.LSeries (_root_.TauCeti.normCoeff K
      (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction))
  · filter_upwards [_root_.self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    rw [hfL (by simpa using hσ), hf₂L (by simpa using hσ)]
    exact _root_.NumberField.Chebotarev.norm_galoisCharacterLSeries_threeFourOne_ge_one χ hσ s.im
  · -- The trivial series has a simple pole at `s = 1`.
    rw [_root_.MonoidHom.galoisCharacterWeight_one]
    exact _root_.TauCeti.isBigO_inv_sub_one_of_tendsto_sub_one_mul <| by
      simpa using _root_.TauCeti.tendsto_sub_one_mul_LSeries_ofBadPrimes (K := K) (_root_.NumberField.Chebotarev.ramifiedPrimes K F)







end NumberField.Chebotarev

end
end
