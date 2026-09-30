-- Prove2me | solution 1 for NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_of_re_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:17:27.183989+00:00
-- url     : https://prove2.me/submissions/592c79e2-8013-4a07-bf38-116ee5749d92

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Data_ZMod_Divisibility
import Definitions.Def_TauCeti_FieldTheory_Galois_Abelian
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Cancellation
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Estimates
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Cyclotomic_Basic
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Cyclotomic_Series
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Ramification
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Sum
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Count_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_ArtinMap
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_NumberTheory_NumberField_TotallyPositive
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Definitions.Def_TauCeti_RingTheory_Frobenius
import Definitions.Def_TauCeti_RingTheory_Ideal_Norm_AbsNorm
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
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
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
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
import Mathlib.NumberTheory.ZetaValues
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
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_NumberField_Chebotarev_cyclotomicArtin_surjective
import Theorems.Thm_NumberField_Chebotarev_cyclotomicCharacterSeriesC_ne_zero_at_one
import Theorems.Thm_NumberField_Chebotarev_ne_zero_of_eqOn_LSeries_galoisCharacterWeight
import Theorems.Thm_TauCeti_GlobalNumberFields_isBigO_rayClassCharacterPartialSum
import Theorems.Thm_TauCeti_LSeriesSummable_normCoeff_one_iff
import Theorems.Thm_TauCeti_LSeries_differentiableOn_mul_integral_of_isBigO
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_LSeries_restrict
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_apply_ne_zero_iff_isGood
import Theorems.Thm_TauCeti_exists_differentiableOn_eq_LSeries_ofBadPrimes_sub
import Theorems.Thm_TauCeti_hasCancellation_iff_isBigO
import Theorems.Thm_TauCeti_idealCount_linearBounds
import Theorems.Thm_TauCeti_idealSummatory_eq_sum_range_normFiber
import Theorems.Thm_TauCeti_sum_norm_normCoeff_one
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





@[simp]
theorem coe_toMonoidWithZeroHom (χ : MultiplicativeIdealWeight K) :
    ⇑χ.toMonoidWithZeroHom = ⇑χ := rfl







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





theorem apply_eq_zero_iff_not_isGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ I = 0 ↔ ¬ χ.IsGood I := by
  rw [← not_ne_iff, χ.apply_ne_zero_iff_isGood]

/-!
### Constructors and operations
-/

section Operations

variable {S : Set (HeightOneSpectrum (𝓞 K))}

























































/-!
### Weights that are norm twists on their good locus
-/

























end Operations

/-!
### Passage to the general carrier, and the zero-ideal rejection test
-/



















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

/-- **A unitary weight has modulus one on every good ideal**, extending its defining condition
from good primes to the entire good-ideal locus. -/
theorem norm_eq_one (χ : UnitaryIdealWeight K) {I : Ideal (𝓞 K)} (hI : χ.1.IsGood I) :
    ‖χ.1 I‖ = 1 := by
  refine hI.induction_on (by simp) fun 𝔭 J h𝔭 _ ih ↦ ?_
  rw [map_mul, norm_mul, χ.2 𝔭 h𝔭, ih, one_mul]

-- Source. The statement and its proof follow `DirichletCharacter.norm_le_one` in Mathlib's
-- `Mathlib/NumberTheory/DirichletCharacter/Bounds.lean`, transposed from a Dirichlet character on
-- `ZMod n` to a unitary ideal weight: the case split there is on `IsUnit a` and closes with
-- `map_nonunit`, here it is on `MultiplicativeIdealWeight.IsGood` and closes with
-- `apply_eq_zero_iff_not_isGood`.

/-- **A unitary weight is bounded by one on every ideal.** The bound is unconditional: it carries
no goodness hypothesis, so a comparison indexed by all of `(Ideal (𝓞 K))⁰` can apply it termwise.
`norm_eq_one` is sharper where it applies, but obliges the caller to split that index type first;
this is the form a convergence estimate wants. -/
theorem norm_le_one (χ : UnitaryIdealWeight K) (I : Ideal (𝓞 K)) : ‖χ.1 I‖ ≤ 1 := by
  by_cases hI : χ.1.IsGood I
  · exact (norm_eq_one χ hI).le
  · rw [(MultiplicativeIdealWeight.apply_eq_zero_iff_not_isGood χ.1 I).mpr hI, norm_zero]
    exact zero_le_one















@[simp]
theorem val_ofPowEqOne (χ : MultiplicativeIdealWeight K) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → χ 𝔭.asIdeal ^ n = 1) :
    (ofPowEqOne χ hn h).1 = χ := (rfl)



















@[simp]
theorem val_restrict (χ : UnitaryIdealWeight K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) : (restrict χ S hS).1 = χ.1.restrict S hS := (rfl)



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
# Finite real-cutoff carriers for Northcott functions

This file packages the finite carrier selected by a real cutoff for a natural-valued Northcott
function, together with generic summatory functions over that carrier. The carrier depends only
on the integer part of the cutoff, and for a nonnegative cutoff it agrees with the one selected by
its natural floor.
-/

 section

namespace TauCeti

open Filter
open scoped Topology

variable {ι : Type*} (N : ι → ℕ) [Northcott N]





/-- An index belongs to `normLE N x` exactly when its `N`-value is at most the inclusive
real cutoff `x`. -/
@[simp, grind =]
theorem mem_normLE {i : ι} {x : ℝ} : i ∈ normLE N x ↔ (N i : ℝ) ≤ x := by
  simp [normLE]

@[simp]
theorem coe_normLE (x : ℝ) : (normLE N x : Set ι) = {i : ι | (N i : ℝ) ≤ x} := by
  ext i
  simp















/-! ### Generic summatory functions -/



/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]





























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







/-! ### The prime base and the exponent of a prime-power ideal -/



























































variable (K)

/-! ### Summatory functions over ideals and over primes -/









/-- An ideal summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem idealSummatory_apply {M : Type*} [AddCommMonoid M] (w : (Ideal (𝓞 K))⁰ → M) (x : ℝ) :
    idealSummatory K w x = ∑ I ∈ idealsLE K x, w I :=
  summatory_apply _ w x























variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)





/-- **An ideal summatory function is a partial sum of norm coefficients.** The inclusive sum of
`f` over the nonzero integral ideals of absolute norm at most `x` is `∑_{n=1}^{⌊x⌋₊}` of the norm
coefficients of `f`, in the `Finset.Icc 1` form of Mathlib's `LSeries_eq_mul_integral`. -/
theorem idealSummatory_eq_sum_Icc_normCoeff (f : IdealArithmeticFunction K) (x : ℝ) :
    idealSummatory K f x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, normCoeff K f n := by
  rw [idealSummatory_eq_sum_range_normFiber, Nat.range_succ_eq_Icc_zero,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), Finset.sum_insert (by simp),
    normFiber_zero, Finset.sum_empty, zero_add, zero_add]
  exact Finset.sum_congr rfl fun n _ ↦ (normCoeff_eq_sum_normFiber K f n).symm



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

/-- The trivial ideal weight has norm coefficient the number of nonzero integral ideals of the
given absolute norm, so its absolute value is that count. -/
theorem norm_normCoeff_one (n : ℕ) :
    ‖normCoeff K (1 : IdealArithmeticFunction K) n‖ = (normFiber K n).card := by
  rw [normCoeff_eq_sum_normFiber]
  simp

/-- The norm coefficients of a unitary weight are bounded in modulus by those of the trivial
weight, which count the ideals of each norm. -/
theorem UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one (χ : UnitaryIdealWeight K) (n : ℕ) :
    ‖normCoeff K χ.toIdealArithmeticFunction n‖ ≤
      ‖normCoeff K (1 : IdealArithmeticFunction K) n‖ := by
  rw [norm_normCoeff_one, normCoeff_eq_sum_normFiber]
  refine (norm_sum_le _ _).trans ?_
  simpa using Finset.sum_le_sum fun I (_ : I ∈ normFiber K n) ↦ χ.norm_le_one (I : Ideal (𝓞 K))



/-! ### The exact abscissa of the trivial ideal weight -/

/-- The upper linear ideal count makes the partial sums of the trivial norm coefficients `O(n)`. -/
theorem isBigO_sum_norm_normCoeff_one :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  obtain ⟨b⟩ := idealCount_linearBounds K
  refine Asymptotics.IsBigO.of_bound b.upper ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [sum_norm_normCoeff_one, Real.rpow_one, Real.norm_natCast, Real.norm_natCast]
  exact b.card_le n h1













/-! ### The exact abscissa, and its Dedekind zeta form -/





/-- The ideal-indexed Dirichlet series of the trivial ideal weight converges absolutely exactly on
`Re s > 1`. -/
theorem summable_idealTerm_one_iff {K : Type*} [Field K] [NumberField K] {s : ℂ} :
    Summable (idealTerm K (1 : IdealArithmeticFunction K) s) ↔ 1 < s.re := by
  refine ⟨fun h ↦ (LSeriesSummable_normCoeff_one_iff K).mp (LSeriesSummable_normCoeff K h),
    fun h ↦ ?_⟩
  exact summable_idealTerm_of_nonneg K 1 (fun _ ↦ zero_le_one)
    ((LSeriesSummable_normCoeff_one_iff K).mpr h)

/-- **A uniformly bounded weight converges wherever the trivial weight does.** If every value of
`f` on a nonzero integral ideal has modulus at most `C`, its ideal-indexed Dirichlet series
converges absolutely on `Re s > 1`.

The bound may be any nonnegative real — a negative `C` makes the hypothesis unsatisfiable, since
`‖f I‖` is a norm — and no `C = 1` normalisation is wanted, since a weight is often bounded by
something other than `1` without being rescaled. The unitary case — a Dirichlet or Galois
character, of modulus `1` at the good primes and `0` at the bad ones — is `C = 1`, and is packaged
as `summable_idealTerm_of_unitary_of_one_lt_re`. Stating the hypothesis here as a bound rather than
as unitarity is what lets the vanishing at the bad primes pass without a special case.

Only one direction holds, unlike `summable_idealTerm_one_iff`: a weight that vanishes identically
is bounded by every nonnegative `C` and converges everywhere. -/
theorem summable_idealTerm_of_bounded_of_one_lt_re {K : Type*} [Field K] [NumberField K]
    {f : IdealArithmeticFunction K} {C : ℝ} (hf : ∀ I : (Ideal (𝓞 K))⁰, ‖f I‖ ≤ C) {s : ℂ}
    (hs : 1 < s.re) : Summable (idealTerm K f s) := by
  refine Summable.of_norm_bounded
    (g := fun I ↦ C * ‖idealTerm K (1 : IdealArithmeticFunction K) s I‖)
    (((summable_idealTerm_one_iff.mpr hs).norm).mul_left C) fun I ↦ ?_
  rw [norm_idealTerm, norm_idealTerm]
  have hpos : (0 : ℝ) < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos (by exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I) _
  have hone : ‖(1 : IdealArithmeticFunction K) I‖ = 1 := by simp
  rw [hone, mul_one_div]
  gcongr
  exact hf I

/-- **A unitary weight converges on `Re s > 1`.** The specialization of
`summable_idealTerm_of_bounded_of_one_lt_re` at `C = 1`, through
`TauCeti.UnitaryIdealWeight.norm_le_one`: a unitary weight has modulus `1` on the good ideals and
vanishes on the rest, so it is bounded by `1` on all of them and the caller is left no case split.

This is the form the Euler-product code consumes, its `hasProd_eulerFactor` asking for exactly a
`Summable (idealTerm K · s)` hypothesis on the weight's passage to `IdealArithmeticFunction`. -/
theorem summable_idealTerm_of_unitary_of_one_lt_re {K : Type*} [Field K] [NumberField K]
    (χ : UnitaryIdealWeight K) {s : ℂ} (hs : 1 < s.re) :
    Summable (idealTerm K χ.toIdealArithmeticFunction s) := by
  refine summable_idealTerm_of_bounded_of_one_lt_re (C := 1) (fun I ↦ ?_) hs
  rw [UnitaryIdealWeight.toIdealArithmeticFunction_apply]
  exact χ.norm_le_one _







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

/-- On `Re s > 0`, `N(𝔭) ^ s` lies outside the closed unit disc. -/
theorem one_lt_norm_absNorm_cpow (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) : 1 < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ s‖ := by
  have hP := NumberField.HeightOneSpectrum.one_lt_absNorm P
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  exact Real.one_lt_rpow (by exact_mod_cast hP) hs







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
# Cancellation in ideal partial sums and the continued L-function of a weight

For a unitary ideal weight `χ` of a number field `K` of degree `d = [K : ℚ]`, the partial sums
`∑_{N(I) ≤ x} χ(I)` over the nonzero integral ideals are trivially `O(x)`, by the linear ideal
count. For nontrivial finite-order ray class characters, equidistribution among ray classes gives
the stronger bound `O(x ^ (1 - 1 / d))`. This file names that bound as a hypothesis and extracts
its analytic consequence.

* `TauCeti.HasCancellation χ` is the uniform bound
  `‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / d)` for every real cutoff `x ≥ 1`, with the inclusive
  summatory function `TauCeti.idealSummatory`.
  Equivalently (`TauCeti.hasCancellation_iff_isBigO`), the partial sums are
  `O(x ^ (1 - 1 / d))` as `x → ∞`.
* `TauCeti.continuedLFunctionOfWeight χ` is the partial-summation integral
  `s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

It agrees with the norm-regrouped L-series of `χ` on `Re s > 1` for *every* unitary weight
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`), and under `HasCancellation χ` it is holomorphic
on `Re s > 1 - 1 / d` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`); so it is an analytic
continuation of the L-series of `χ` across the line `Re s = 1`.

Both are stable under deleting finitely many Euler factors, the operation a character family
needs at the bad primes of its modulus. A one-prime recurrence relates the partial sums after
inserting a forbidden prime to two partial sums before the insertion
(`TauCeti.MultiplicativeIdealWeight.idealSummatory_restrict_insert`). Iterating this recurrence
shows that cancellation passes to the restriction (`TauCeti.HasCancellation.restrict`); on
`Re s > 1` the two continued
`L`-functions differ by the entire factor `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))`
(`TauCeti.continuedLFunctionOfWeight_restrict_of_one_lt_re`), and under cancellation that identity
propagates to the whole half-plane `Re s > 1 - 1 / d`
(`TauCeti.continuedLFunctionOfWeight_restrict`).

In number-field degree greater than one, cancellation is also invariant under purely imaginary
norm twists (`TauCeti.hasCancellation_normTwist_iff`). Abel summation supplies this because the
cancellation exponent `1 - 1 / [K : ℚ]` is then positive. The degree-one case is deliberately not
claimed: the defining bound has exponent zero, while the absolute bound for the Abel integral is
logarithmic.

The continued `L`-function itself follows these operations. Conjugating the weight reflects it
in the real axis, `L(conj χ, conj s) = conj (L(χ, s))`, at every `s`
(`TauCeti.continuedLFunctionOfWeight_conj`). An imaginary norm twist by `N(I) ^ (-z)` translates
it by `z`: on `Re s > 1` for every weight
(`TauCeti.continuedLFunctionOfWeight_normTwist_of_one_lt_re`), and on the whole half-plane
`Re s > 1 - 1 / d` when both the weight and its twist have cancellation
(`TauCeti.continuedLFunctionOfWeight_normTwist`).

Cancellation is a hypothesis about the partial sums themselves. It cannot be replaced by
finiteness of the image of `χ` or of a quotient through which it factors: the values of a weight
factoring through a finite quotient of the free group on the prime ideals can be prescribed
arbitrarily prime by prime.

Nor is it automatic, and `TauCeti.not_hasCancellation_of_isNormTwistOnGood` says which weights it
excludes: those agreeing with a norm twist `I ↦ N(I) ^ (u * I)` on the ideals prime to their bad
primes. The `L`-series of such a weight is the Dedekind zeta function with finitely many Euler
factors deleted, read at `s - u * I`, so it has a pole at `s = 1 + u * I`, where cancellation
would instead make `continuedLFunctionOfWeight χ` holomorphic. The trivial weight
(`TauCeti.not_hasCancellation_one`) and its purely imaginary norm twists
(`TauCeti.not_hasCancellation_normTwist_one`) are the cases a character-family argument meets:
it must not assume cancellation for the degenerate members of its family.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1 (partial summation).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII §6, for the partial-sum bound of finite-order
  ray class character L-series.
-/

 section

namespace TauCeti

open _root_.Filter _root_.Asymptotics _root_.IsDedekindDomain _root_.MeasureTheory
open scoped _root_.ComplexConjugate _root_.nonZeroDivisors _root_.NumberField _root_.Topology

variable {K : Type*} [Field K] [NumberField K]















/-!
### Deleting finitely many Euler factors
-/



/-- **Cancellation bounds the partial sums of the norm coefficients**, in the `O(n ^ r)` form of
Mathlib's `LSeries_eq_mul_integral`. -/
theorem HasCancellation.isBigO_sum_normCoeff {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, normCoeff K χ.toIdealArithmeticFunction k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC⟩ := hχ
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← Nat.floor_natCast (R := ℝ) n, ← idealSummatory_eq_sum_Icc_normCoeff, Nat.floor_natCast,
    Real.norm_of_nonneg (by positivity)]
  exact hC n (by exact_mod_cast hn)



/-- The continued L-function as the integral of Mathlib's `LSeries_eq_mul_integral`, over the
partial sums of the norm coefficients. -/
theorem continuedLFunctionOfWeight_eq_mul_integral (χ : UnitaryIdealWeight K) (s : ℂ) :
    continuedLFunctionOfWeight χ s = s * ∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, normCoeff K χ.toIdealArithmeticFunction k) *
        (t : ℂ) ^ (-(s + 1)) := by
  simp only [continuedLFunctionOfWeight, idealSummatory_eq_sum_Icc_normCoeff]

/-- **The continued L-function is the L-series on `Re s > 1`.** For every unitary weight, with or
without cancellation, `continuedLFunctionOfWeight χ` agrees with the `LSeries` of the norm
coefficients of `χ` to the right of `1`, where that series converges absolutely. -/
theorem continuedLFunctionOfWeight_eq_LSeries (χ : UnitaryIdealWeight K) {s : ℂ}
    (hs : 1 < s.re) :
    continuedLFunctionOfWeight χ s = LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  rw [continuedLFunctionOfWeight_eq_mul_integral]
  refine (LSeries_eq_mul_integral' _ zero_le_one (by simpa using hs) ?_).symm
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ ?_)).trans
    (isBigO_sum_norm_normCoeff_one K)
  rw [one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
  exact Finset.sum_le_sum fun k _ ↦
    UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one K χ k

/-- **Cancellation continues the L-series of a weight.** If `χ` has cancellation, its continued
L-function is holomorphic on the half-plane `Re s > 1 - 1 / [K : ℚ]`, which contains the line
`Re s = 1`. -/
theorem differentiableOn_continuedLFunctionOfWeight {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) :
    DifferentiableOn ℂ (continuedLFunctionOfWeight χ)
      {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
  rw [funext (continuedLFunctionOfWeight_eq_mul_integral χ)]
  exact LSeries.differentiableOn_mul_integral_of_isBigO _ hχ.isBigO_sum_normCoeff

/-- **Deleting finitely many Euler factors, to the right of `1`.** Where the norm-regrouped series
converge absolutely, restricting a unitary weight away from a finite set `S` of primes multiplies
its continued `L`-function by the reciprocals `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))` of the deleted
local factors. -/
theorem continuedLFunctionOfWeight_restrict_of_one_lt_re (χ : UnitaryIdealWeight K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    continuedLFunctionOfWeight
        (χ.restrict (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet) s =
      continuedLFunctionOfWeight χ s *
        ∏ 𝔭 ∈ S, (1 - χ.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) := by
  rw [continuedLFunctionOfWeight_eq_LSeries _ hs, continuedLFunctionOfWeight_eq_LSeries _ hs,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_restrict]
  exact χ.1.LSeries_restrict S (by
    rw [← UnitaryIdealWeight.toIdealArithmeticFunction_eq_val]
    exact summable_idealTerm_of_unitary_of_one_lt_re χ hs)



/-!
### Conjugation and imaginary norm twists
-/







/-!
### The rejection test: weights that are norm twists on their good ideals
-/









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
# The ray class group of a modulus

Let `𝔪` be a modulus of a number field `K`.  The **ray** of `𝔪` is the subgroup of principal
fractional ideals generated by the elements of `Kˣ` congruent to one modulo `𝔪`, and the **ray
class group** `RayClassGroup 𝔪` is the quotient of the group `idealsPrimeTo 𝔪` of invertible
fractional ideals prime to the finite part of `𝔪` by that ray.

The ray really is a subgroup of `idealsPrimeTo 𝔪`, and not merely of all invertible fractional
ideals: an element congruent to one is a unit at every prime dividing the finite part of `𝔪`
(`IsCongrOne.valuation_eq_one`), so its principal ideal has vanishing multiplicity there.  That is
the content of `TauCeti.GlobalNumberFields.rayHom`, from which the ray is obtained as a range.

The class of an ideal is defined on the monoid `integralIdealsPrimeTo 𝔪` of nonzero integral ideals
prime to the finite part, never on all of `Ideal (𝓞 K)`: an ideal sharing a prime with the finite
part has no ray class, and carrying the coprimality proof in the argument makes multiplicativity
literally `map_mul`.

For the trivial modulus the congruence condition is empty, and the ray class group is the ordinary
class group (`oneEquivClassGroup`).

## Main definitions

* `TauCeti.GlobalNumberFields.principalIdealPrimeTo`: the principal fractional ideals whose
  generators are units at the finite part.
* `TauCeti.GlobalNumberFields.rayHom`, `TauCeti.GlobalNumberFields.ray`: the principal ideals of
  the elements congruent to one, and the subgroup they form.
* `TauCeti.GlobalNumberFields.idealsPrimeToClassGroup`: the ordinary ideal class of an invertible
  fractional ideal prime to a modulus.
* `TauCeti.GlobalNumberFields.RayClassGroup`: the quotient of `idealsPrimeTo 𝔪` by the ray, with
  `TauCeti.GlobalNumberFields.rayClassMk` and the universal property
  `TauCeti.GlobalNumberFields.rayClassLift`.
* `TauCeti.GlobalNumberFields.idealClass`: the ray class of an integral ideal prime to `𝔪`, as a
  monoid homomorphism out of `integralIdealsPrimeTo 𝔪`.
* `TauCeti.GlobalNumberFields.classMap`: the transition map, running from the ray class group of a
  larger modulus to that of a divisor of it.

## Main results

* `TauCeti.GlobalNumberFields.toPrincipalIdeal_mem_idealsPrimeTo_iff`: a principal fractional ideal
  is prime to the modulus exactly when its generator is a unit at every prime dividing the finite
  part, with `TauCeti.GlobalNumberFields.IsCongrOne.toPrincipalIdeal_mem_idealsPrimeTo` the
  consequence for an element congruent to one.
* `TauCeti.GlobalNumberFields.idealsPrimeTo_eq_top`: every invertible fractional ideal is prime
  to a modulus whose support is empty, so `TauCeti.GlobalNumberFields.idealsPrimeToEquiv`
  identifies the two carriers there.
* `TauCeti.GlobalNumberFields.idealClass_apply`: the ray class of an integral ideal is the ray
  class of the fractional ideal it generates.
* `TauCeti.GlobalNumberFields.idealClass_mul`: taking the ray class of an integral ideal respects
  multiplication.
* `TauCeti.GlobalNumberFields.idealClass_eq_one_iff`: an ideal has trivial ray class exactly when
  it is generated, as a fractional ideal, by an element of `Kˣ` congruent to one modulo `𝔪`.
* `TauCeti.GlobalNumberFields.classMap_comp_classMap` and
  `TauCeti.GlobalNumberFields.classMap_comp_idealClass`: the transition maps compose along a tower
  of moduli, and carry the class of an integral ideal to the class of the same ideal.  Both are
  equalities of homomorphisms, with the pointwise forms `classMap_classMap` and
  `classMap_idealClass` derived from them.  The transition map from a modulus to itself is the
  identity (`TauCeti.GlobalNumberFields.classMap_refl`).
* `TauCeti.GlobalNumberFields.oneEquivClassGroup`: at the trivial modulus the ray class group is
  the class group of `𝓞 K`, carrying a ray class to the class of the same fractional ideal
  (`TauCeti.GlobalNumberFields.oneEquivClassGroup_rayClassMk`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open _root_.IsDedekindDomain _root_.IsDedekindDomain.HeightOneSpectrum _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]





































@[simp] theorem rayClassLift_rayClassMk {M : Type*} [Monoid M] {𝔪 : Modulus K}
    (φ : idealsPrimeTo 𝔪 →* M) (h : ray 𝔪 ≤ φ.ker) (I : idealsPrimeTo 𝔪) :
    rayClassLift φ h (rayClassMk 𝔪 I) = φ I := (rfl)









/-- The ray class of an integral ideal is the ray class of the fractional ideal it generates. -/
theorem idealClass_apply (𝔪 : Modulus K) (I : integralIdealsPrimeTo 𝔪) :
    idealClass 𝔪 I = rayClassMk 𝔪 (NumberFieldArithmetic.integralIdealsAwayHom 𝔪.support I) :=
  (rfl)



/-! ### The transition map between ray class groups -/

















/-! ### Moduli with unit finite part -/









/-! ### The trivial modulus -/







end TauCeti.GlobalNumberFields

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
# Ray class characters

A ray class character of a modulus `𝔪` is a multiplicative character of its finite ray class
group with values in the complex units.  Composing with `idealClass 𝔪` evaluates it on the
nonzero integral ideals prime to the finite part of `𝔪`; the coprimality proof remains in the
domain because `idealClass 𝔪` is defined only on those ideals.

When `𝔪 ∣ 𝔫`, pullback along the surjective transition `classMap : Cl_𝔫 → Cl_𝔪` induces a
character of the larger modulus.  These pullbacks are injective, compose along chains of moduli,
and agree with the inclusion of integral ideals prime to the larger modulus.  This is the finite
character API used in ray-class counting and in the factorization of cyclotomic Galois
characters.

## Main definitions

* `TauCeti.GlobalNumberFields.RayClassCharacter`: multiplicative complex-unit characters of a
  ray class group;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals`: evaluation on integral ideals prime
  to the modulus;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced`: pullback of a character along a change
  of modulus.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.ext`: a ray class character is
  determined by its values on integral ideals;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced_injective`: increasing the modulus does
  not identify distinct characters;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals_induced`: change of modulus commutes
  with evaluation on ideals.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VII, §1.
-/

 section

open scoped _root_.NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]



namespace RayClassCharacter

variable {𝔪 𝔫 𝔬 : Modulus K}



/-- Evaluating a ray class character on an ideal is evaluation at the ideal's ray class. -/
@[simp]
theorem onIdeals_apply (χ : RayClassCharacter 𝔪) (I : integralIdealsPrimeTo 𝔪) :
    χ.onIdeals I = χ (idealClass 𝔪 I) :=
  by simp [onIdeals]

















end RayClassCharacter

end TauCeti.GlobalNumberFields

end
end

section
set_option autoImplicit true
namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
namespace TauCeti.NumberFieldArithmetic
end TauCeti.NumberFieldArithmetic
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cyclotomic Galois characters as ray class characters

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K`, and let `𝔪` be the
modulus of `K` with finite part `(m)` and every real place in its infinite part. This file
provides the Artin map of the abelian extension `F / K` as a homomorphism from the ray class group
of `𝔪` to `Gal(F/K)`. It sends the ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`.

Composing with it, every character `χ` of `Gal(F/K)` gives a ray class character of `𝔪`, and on
the integral ideals prime to `m` the ideal weight `galoisCharacterWeight χ` of `χ` agrees with that
ray class character.

## Main definitions

* `NumberField.Chebotarev.cyclotomicModulus`: the modulus of `K` with finite part `(m)` and
  every real place in its infinite part.
* `NumberField.Chebotarev.cyclotomicArtin`: the Artin map
  `RayClassGroup (cyclotomicModulus K m) →* (F ≃ₐ[K] F)`.

## Main results

* `NumberField.Chebotarev.cyclotomicArtin_idealClass_of_isArithFrobAt`: the Artin map sends the
  ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`.
* `MonoidHom.galoisCharacterWeight_eq_onIdeals_cyclotomicArtin`: on the integral ideals prime to
  `m`, the ideal weight of a character `χ` of `Gal(F/K)` is the ray class character
  `χ ∘ cyclotomicArtin`.
-/

 section

open _root_.IsDedekindDomain _root_.IsDedekindDomain.HeightOneSpectrum _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

namespace NumberField.Chebotarev

open _root_.TauCeti.GlobalNumberFields _root_.TauCeti.NumberFieldArithmetic

section Modulus

variable (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m]







variable {K m}





end Modulus

section Auxiliary

variable {K : Type*} [Field K] [NumberField K]

-- A nonzero integer congruent to one modulo `(m)` generates an ideal prime to the cyclotomic
-- modulus.


end Auxiliary

section Cyclotomic



variable {K : Type*} [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F]
  [Algebra K F] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- The Artin map of `F / K` on the fractional ideals prime to `m`.


-- The Artin map of `F / K` on the integral ideals prime to `m`.


-- The integral Artin map is the fractional one read on the ideals the integral ones generate.


-- At a prime not dividing `m`, the integral Artin map is the Frobenius.


-- The cyclotomic character of the integral Artin map is the absolute norm.


-- The Artin map of `F / K` kills the ray of the cyclotomic modulus.




-- On the ray class of an integral ideal, `cyclotomicArtin` is the integral Artin map.
private theorem cyclotomicArtin_idealClass (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    cyclotomicArtin K F m (idealClass _ I) = cyclotomicArtinIntegral F m I := by
  rw [idealClass_apply, cyclotomicArtin, rayClassLift_rayClassMk, cyclotomicArtinIntegral_apply]

/-- **The Artin map sends the ray class of a prime to its Frobenius.** At a height-one prime `𝔭`
not dividing `m`, every arithmetic Frobenius at every prime of `𝓞 F` above `𝔭` is the image of
the ray class of `𝔭`. -/
theorem cyclotomicArtin_idealClass_of_isArithFrobAt (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭 : 𝔭.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m)) (Q : Ideal (𝓞 F)) [Q.IsPrime]
    [Q.LiesOver 𝔭.asIdeal] {σ : F ≃ₐ[K] F} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    cyclotomicArtin K F m (idealClass _ ⟨𝔭.asIdeal, h𝔭⟩) = σ := by
  rw [cyclotomicArtin_idealClass, cyclotomicArtinIntegral_of_isArithFrobAt F m 𝔭 h𝔭 Q hσ]

end Cyclotomic

end NumberField.Chebotarev

namespace MonoidHom

open _root_.TauCeti.GlobalNumberFields _root_.TauCeti.NumberFieldArithmetic _root_.NumberField.Chebotarev
open scoped _root_.IsMulCommutative

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- At a prime `v ∤ m`, the ideal weight of `χ` is `χ` of the Artin image of the ray class of `v`.
private theorem galoisCharacterWeight_asIdeal_eq_cyclotomicArtin (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m)) :
    galoisCharacterWeight (L := F) χ v.asIdeal =
      (χ (cyclotomicArtin K F m (idealClass _ ⟨v.asIdeal, hv⟩)) : ℂ) := by
  have hur : ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q := fun Q _ _ ↦
    isUnramifiedAt_of_notMem_cyclotomicModulus_support F m
      (mem_cyclotomicModulus_support_iff.not.mpr
        (asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv)) Q
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 F)))
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  -- `Gal(F/K)` is abelian, so the Artin symbol at `v` is the singleton class of `σ`
  rw [galoisCharacterWeight_apply_of_unramified χ v hur,
    cyclotomicArtin_idealClass_of_isArithFrobAt F m v hv Q hσ,
    isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ((Quotient.out_eq _).trans
      (artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal hur Q σ hσ)))]

/-- **The ideal weight of a cyclotomic Galois character is a ray class character.** For a
character `χ` of `Gal(F/K)` with `F = K(μ_m)`, the ideal weight `galoisCharacterWeight χ` agrees,
on the integral ideals prime to `m`, with the ray class character `χ ∘ cyclotomicArtin K F m` of
`cyclotomicModulus K m`. -/
theorem galoisCharacterWeight_eq_onIdeals_cyclotomicArtin (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    galoisCharacterWeight (L := F) χ (I : Ideal (𝓞 K)) =
      (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ) := by
  -- both sides are multiplicative in `I`, and they agree on the primes `v ∤ m`
  let f : integralIdealsPrimeTo (cyclotomicModulus K m) →* ℂ :=
    (galoisCharacterWeight (L := F) χ).toMonoidWithZeroHom.toMonoidHom.comp
      (integralIdealsPrimeTo (cyclotomicModulus K m)).subtype
  let g : integralIdealsPrimeTo (cyclotomicModulus K m) →* ℂ :=
    (Units.coeHom ℂ).comp (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)))
  have hfg : f = g := integralIdealsAway_hom_ext fun v hv ↦ by
    simpa [f, g, TauCeti.MultiplicativeIdealWeight.coe_toMonoidWithZeroHom] using
      galoisCharacterWeight_asIdeal_eq_cyclotomicArtin χ v hv
  exact DFunLike.congr_fun hfg I

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
# Character sums over the integral ideals of bounded norm

Let `𝔪` be a modulus of a number field `K` and `χ` a ray class character of `𝔪`.  This file
introduces `rayClassCharacterPartialSum 𝔪 χ x`, the sum of `χ` over the nonzero integral ideals
prime to the finite part of `𝔪` whose norm is at most `x`, and identifies it with the
`χ`-weighted combination of the ray class counting functions.

The sum ranges over ideals, not over chosen class representatives.  Regrouping it by ray class is
exactly the partition `idealClassSigmaEquiv`, and on each fibre `χ` is constant, so each class
contributes its counting function scaled by the single value `χ` takes there.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum`: the partial sum of a ray class
  character over the integral ideals of bounded norm.

## Main results

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_eq_sum`: the partial sum is
  `∑ c, χ c * rayClassIdealCountingFunction 𝔪 c x`.
-/

 section

namespace TauCeti.GlobalNumberFields

open scoped _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]



open scoped Classical in
/-- **The partial sum as the `finsum` defining it.**  The rewrite rule turning
`rayClassCharacterPartialSum` into the sum of `χ.onIdeals` over the integral ideals prime to `𝔪`
of norm at most `x`. -/
theorem rayClassCharacterPartialSum_def (𝔪 : Modulus K) (χ : RayClassCharacter 𝔪) (x : ℝ) :
    rayClassCharacterPartialSum 𝔪 χ x =
      ∑ᶠ I : {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x},
        (χ.onIdeals (I : integralIdealsPrimeTo 𝔪) : ℂ) := by
  rw [rayClassCharacterPartialSum, summatory_apply, ← finsum_mem_coe_finset, coe_normLE]
  exact (finsum_set_coe_eq_finsum_mem _).symm



end TauCeti.GlobalNumberFields

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cancellation for the ideal weight of a cyclotomic Galois character

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K` and `χ` a character of
`Gal(F/K)` whose ray class character `χ ∘ cyclotomicArtin K F m` of `cyclotomicModulus K m` is
nontrivial. This file provides cancellation for the ideal weight `galoisCharacterUnitaryWeight χ`
with its Euler factors at the primes dividing `m` deleted: its ideal partial sums are
`O(x ^ (1 - 1 / [K : ℚ]))`. At such a prime the weight can be a root of unity rather than `0` (the
prime may be unramified in `F`), so the restricted weight is the one that agrees with the ray class
character.

## Main results

* `MonoidHom.hasCancellation_restrict_galoisCharacterUnitaryWeight`: the weight restricted away
  from the primes dividing `m` has cancellation.
-/

 section

open _root_.IsDedekindDomain _root_.TauCeti _root_.TauCeti.GlobalNumberFields _root_.NumberField.Chebotarev
open scoped _root_.nonZeroDivisors _root_.NumberField

namespace MonoidHom

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- The ideal partial sums of the Galois weight with the Euler factors at the primes dividing `m`
-- deleted are the partial sums of the ray class character `χ ∘ cyclotomicArtin K F m`.
private theorem idealSummatory_restrict_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (x : ℝ) :
    idealSummatory K ((galoisCharacterUnitaryWeight (L := F) χ).restrict
        ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
        (cyclotomicModulus K m).support.finite_toSet).toIdealArithmeticFunction x =
      rayClassCharacterPartialSum (cyclotomicModulus K m) (χ.comp (cyclotomicArtin K F m)) x := by
  classical
  set 𝔪 := cyclotomicModulus K m
  have hmem (J : Ideal (𝓞 K)) : J ∈ integralIdealsPrimeTo 𝔪 ↔ J.IsPrimeTo 𝔪.support :=
    NumberFieldArithmetic.mem_integralIdealsAway_iff.trans Ideal.isPrimeTo_iff.symm
  let e : integralIdealsPrimeTo 𝔪 → (Ideal (𝓞 K))⁰ := fun I ↦
    ⟨I, mem_nonZeroDivisors_of_ne_zero ((hmem I).mp I.2).ne_bot⟩
  have hsum : rayClassCharacterPartialSum 𝔪 (χ.comp (cyclotomicArtin K F m)) x =
      ∑ I ∈ normLE (fun I : integralIdealsPrimeTo 𝔪 ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x,
        (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ) := by
    rw [rayClassCharacterPartialSum_def, ← finsum_mem_coe_finset, coe_normLE]
    exact finsum_set_coe_eq_finsum_mem
      (f := fun I ↦ (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ)) _
  rw [hsum, idealSummatory_apply]
  refine (Finset.sum_of_injOn e (fun I _ J _ h ↦ Subtype.ext (by simpa [e] using h))
    (fun I hI ↦ by simpa [e] using hI) (fun J hJ hJe ↦ ?_) (fun I _ ↦ ?_)).symm
  · simpa using fun hJ𝔪 ↦ absurd ⟨⟨J, (hmem J).mpr hJ𝔪⟩, by simpa using hJ, rfl⟩ hJe
  · simpa [e, 𝔪, (hmem I).mp I.2] using (galoisCharacterWeight_eq_onIdeals_cyclotomicArtin χ I).symm

/-- **Cancellation for a cyclotomic Galois character, away from the level.** For `F = K(μ_m)`
and a character `χ` of `Gal(F/K)` whose ray class character `χ ∘ cyclotomicArtin K F m` is
nontrivial, the ideal weight of `χ` with the Euler factors at the primes dividing `m` deleted has
cancellation. -/
theorem hasCancellation_restrict_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ.comp (cyclotomicArtin K F m) ≠ 1) :
    HasCancellation ((galoisCharacterUnitaryWeight (L := F) χ).restrict
      ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
      (cyclotomicModulus K m).support.finite_toSet) := by
  simpa [hasCancellation_iff_isBigO, idealSummatory_restrict_galoisCharacterUnitaryWeight] using
    isBigO_rayClassCharacterPartialSum _ _ hχ

end MonoidHom

end
end

section
set_option autoImplicit true
namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Dedekind zeta function across the line `Re s = 1`

Let `K` be a number field of degree `d = [K : ℚ]`. The number of nonzero integral ideals of `𝓞 K`
of absolute norm at most `x` is `ρ x + O(x ^ (1 - 1 / d))`, where `ρ = dedekindZeta_residue K`:
summing the ray class ideal counts over the classes of the trivial modulus recovers the total
count, and every class has the same main term.

By partial summation this power saving continues the Dedekind zeta function across the line
`Re s = 1`, with a single simple pole there. Comparing the Dirichlet coefficients of `ζ_K` with
`ρ` times those of the Riemann zeta function, the difference has partial sums `O(n ^ (1 - 1 / d))`,
so its `L`-series continues holomorphically to `Re s > 1 - 1 / d`; and `ζ(s) - 1 / (s - 1)` is
entire (Mathlib's `riemannZeta₀`). Hence `ζ_K(s) - ρ / (s - 1)` agrees on `Re s > 1` with a
function holomorphic on `Re s > 1 - 1 / d`.

Deleting finitely many Euler factors multiplies `ζ_K` by the entire function
`∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`, so the Dedekind zeta function with the Euler factors at a finite set
`S` of primes deleted has the same kind of continuation, with residue
`ρ * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-1))` at its simple pole `s = 1`. This is the `L`-series of the trivial
member of a family of ideal weights with bad primes `S`, such as the trivial Galois character of a
Galois extension, whose bad primes are the ramified ones.

## Main results

* `TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re`: the closed half-plane
  `Re s ≥ 1` lies in the half-plane of continuation.
* `TauCeti.isBigO_card_idealsLE_sub`: the number of nonzero integral ideals of norm at most `x` is
  `ρ x + O(x ^ (1 - 1 / [K : ℚ]))`.
* `TauCeti.exists_differentiableOn_eq_dedekindZeta_sub`: `ζ_K(s) - ρ / (s - 1)` extends
  holomorphically from `Re s > 1` to `Re s > 1 - 1 / [K : ℚ]`.
* `TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub`: the same for the Dedekind zeta
  function with the Euler factors at a finite set of primes deleted, with the correspondingly
  corrected residue.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI and Chapter VIII, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti.GlobalNumberFields
open scoped _root_.nonZeroDivisors

namespace TauCeti

/-- The closed half-plane `Re s ≥ 1` lies in the half-plane of the Dedekind zeta continuation. -/
theorem setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re
    (K : Type*) [Field K] [NumberField K] :
    {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} :=
  fun _ hs ↦
    (sub_lt_self (1 : ℝ) (one_div_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))).trans_le hs

variable (K : Type*) [Field K] [NumberField K]

-- The nonzero integral ideals of norm at most `x` are those prime to the trivial modulus.




-- The Dirichlet coefficients of `ζ_K` minus `ρ` times those of the Riemann zeta function have
-- partial sums `O(n ^ (1 - 1 / [K : ℚ]))`.






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
# The continued L-series of a cyclotomic Galois character

For a finite Galois extension `F / K` of number fields and a character `χ` of `Gal(F/K)`,
`cyclotomicCharacterSeriesC K F χ` is a holomorphic continuation of the `L`-series of the ideal
weight `galoisCharacterWeight χ` to the half-plane `Re s > 1 - 1 / [K : ℚ]` when one exists, and
the `L`-series itself otherwise. For every `χ` it agrees with the `L`-series on `Re s > 1`.

For a cyclotomic extension `F = K(μ_m)` and a nontrivial character `χ`, the continuation exists,
so the series is analytic at `s = 1`, and its value at `s = 1` is nonzero. For the trivial
character the series is the Dedekind zeta function of `K` with the Euler factors at the ramified
primes deleted, which continues across `Re s = 1` apart from a single simple pole at `s = 1`.

## Main definitions

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC`: the continued `L`-series of a Galois
  character.

## Main results

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_eq_LSeries`: on `Re s > 1` it is the
  `L`-series of `galoisCharacterWeight χ`.
* `NumberField.Chebotarev.logDeriv_cyclotomicCharacterSeriesC`: the logarithmic derivative
  agrees with that of the character `L`-series on `Re s > 1`.
* `NumberField.Chebotarev.differentiableOn_cyclotomicCharacterSeriesC`: for `F = K(μ_m)` and
  `χ` nontrivial it is holomorphic on `Re s > 1 - 1 / [K : ℚ]`.
* `NumberField.Chebotarev.analyticAt_cyclotomicCharacterSeriesC_one`: for `F = K(μ_m)` and `χ`
  nontrivial it is analytic at `s = 1`.
* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_at_one`: for `F = K(μ_m)` and `χ`
  nontrivial it is nonzero at `s = 1`.

## References

* The nonvanishing argument at `s = 1`, in which the logarithm of the product of the `L`-series
  over all characters is a series with nonnegative coefficients that is unbounded as `s → 1⁺`, is
  analogous to `Chebotarev.artinLSeries_one_ne_zero` in AINTLIB (`github.com/CBirkbeck/aintlib`
  at commit `8102fa09bbf570f3e991adfdb2d6d70b48cb5b5e`, Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ZetaProduct.lean`, which proves the nonvanishing at
  `s = 1` of the Artin `L`-series of a nontrivial character of `Gal(K(μ_m)/K)`.
-/

 section

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.Topology

namespace NumberField.Chebotarev

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]



variable {K F}

variable (K F) in
/-- **The continued `L`-series is the `L`-series on `Re s > 1`.** This holds for every Galois
extension `F / K` and every character `χ`, with no cyclotomic hypothesis. -/
@[simp]
theorem cyclotomicCharacterSeriesC_eq_LSeries (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    cyclotomicCharacterSeriesC K F χ s =
      LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s := by
  rw [cyclotomicCharacterSeriesC]
  split_ifs with h
  exacts [h.choose_spec.2 s hs, rfl]



-- The continuation exists for a nontrivial ray class character: for `F = K(μ_m)` and a character
-- `χ` of `Gal(F/K)` with `χ ∘ cyclotomicArtin K F m` nontrivial, the `L`-series of the weight of
-- `χ` has a holomorphic continuation to `Re s > 1 - 1 / [K : ℚ]`.
private theorem exists_differentiableOn_eq_LSeries (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ.comp (cyclotomicArtin K F m) ≠ 1) : ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧ ∀ s : ℂ, 1 < s.re → f s =
        LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s := by
  set S := (cyclotomicModulus K m).support
  set w := χ.galoisCharacterUnitaryWeight
  have hcorr : Differentiable ℂ
      fun s : ℂ ↦ ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) :=
    Differentiable.fun_finsetProd fun 𝔭 _ ↦ (differentiable_const 1).sub
      ((differentiable_const _).div (differentiable_id.const_cpow (.inl 𝔭.natCast_absNorm_ne_zero))
        fun s ↦ by simp [Complex.cpow_eq_zero_iff, 𝔭.natCast_absNorm_ne_zero])
  -- On `Re s > 0` each local factor `1 - w(𝔭) N(𝔭) ^ (-s)` is nonzero, since `‖w(𝔭)‖ ≤ 1`.
  have hne {s : ℂ} (hs : 0 < s.re) :
      ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun 𝔭 _ ↦ (isUnit_one_sub_of_norm_lt_one <| by
      rw [norm_div, div_lt_one (zero_lt_one.trans (𝔭.one_lt_norm_absNorm_cpow hs))]
      exact (w.norm_le_one _).trans_lt (𝔭.one_lt_norm_absNorm_cpow hs)).ne_zero
  -- The continued `L`-function with the Euler factors at the primes dividing `m` deleted has
  -- cancellation; dividing by those factors, which are nonzero on `Re s > 0`, restores them.
  refine ⟨fun s ↦ continuedLFunctionOfWeight (w.restrict (S : Set _) S.finite_toSet) s /
      ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s), ?_, fun s hs ↦ ?_⟩
  · refine (differentiableOn_continuedLFunctionOfWeight
      (MonoidHom.hasCancellation_restrict_galoisCharacterUnitaryWeight χ hχ)).div
        hcorr.differentiableOn fun s hs ↦ hne ?_
    -- The half-plane `Re s > 1 - 1 / [K : ℚ]` lies in `Re s > 0`.
    exact (sub_nonneg.mpr <| div_le_one_of_le₀ (Nat.one_le_cast.mpr Module.finrank_pos)
      (Nat.cast_nonneg _)).trans_lt hs
  · dsimp only
    rw [continuedLFunctionOfWeight_restrict_of_one_lt_re w S hs,
      mul_div_cancel_right₀ _ (hne (by linarith)), continuedLFunctionOfWeight_eq_LSeries _ hs,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      MonoidHom.val_galoisCharacterUnitaryWeight]

variable (K F) in
/-- **Holomorphy on `Re s > 1 - 1 / [K : ℚ]`.** For `F = K(μ_m)` and a nontrivial character `χ` of
`Gal(F/K)`, the continued `L`-series of `χ` is holomorphic on the half-plane
`Re s > 1 - 1 / [K : ℚ]`. -/
theorem differentiableOn_cyclotomicCharacterSeriesC (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (cyclotomicCharacterSeriesC K F χ)
      {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
  -- The Artin map is surjective, so `χ ∘ cyclotomicArtin K F m` is nontrivial.
  have h := exists_differentiableOn_eq_LSeries m χ <| by
    rwa [Ne, ← MonoidHom.one_comp (cyclotomicArtin K F m),
      MonoidHom.cancel_right (cyclotomicArtin_surjective K F m)]
  rw [cyclotomicCharacterSeriesC]
  split_ifs
  exact h.choose_spec.1



-- As `s → 1⁺`, the prime sum over the primes of `K` that split completely in `F` tends to infinity.


-- At a completely split prime the Frobenius class is trivial, so its chosen representative is `1`.


-- The character sum of a power of the Galois weights at a prime is a nonnegative real number, and
-- at a completely split prime the sum of the weights themselves is `#Gal(F/K)`.


-- For `σ > 1`, summing over the characters the Euler-product logarithm series of their `L`-series
-- gives the real series `∑_{P, e} r(P, e) / (N(P) ^ σ) ^ (e + 1) / (e + 1)`, where `r(P, e)` is
-- the character sum of the `(e + 1)`-th powers of the weights at `P`.


-- For `F / K` abelian, the product over all characters `ψ` of `Gal(F/K)` of the `L`-series of
-- `galoisCharacterWeight ψ` tends to infinity in norm as `s → 1⁺` along the reals.






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

variable (K F) in
-- The series of the trivial character continues to a function differentiable at every point of
-- `Re s = 1` other than the pole `s = 1`.
private theorem exists_differentiableAt_eqOn_LSeries_galoisCharacterWeight_one :
    ∃ T : ℂ → ℂ, (∀ s : ℂ, s.re = 1 → s ≠ 1 → DifferentiableAt ℂ T s) ∧
      Set.EqOn T (LSeries (normCoeff K
        (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction))
        {s | 1 < s.re} := by
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_LSeries_ofBadPrimes_sub K (ramifiedPrimes K F)
  set ρ := dedekindZeta_residue K *
    ∏ 𝔭 ∈ ramifiedPrimes K F, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-1 : ℂ))
  refine ⟨fun s ↦ G s + ρ / (s - 1), fun s hs hs1 ↦ ?_, fun s (hs : 1 < s.re) ↦ ?_⟩
  · -- The line `Re s = 1` lies in the half-plane `Re s > 1 - 1 / [K : ℚ]` of the continuation.
    have hmem : {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const continuous_re).mem_nhds <| by
        rw [Set.mem_ofPred_eq, hs]
        simpa only [Set.mem_ofPred_eq, hs] using
          setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.ge
    exact (hG.differentiableAt hmem).add
      ((differentiableAt_const ρ).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
  · dsimp only
    rw [hGL s hs, MonoidHom.galoisCharacterWeight_one, sub_add_cancel]



/-- **Nonvanishing on `Re s = 1` for a character of order at most two.** Let `F / K` be a finite
Galois extension and `χ` a character of `Gal(F/K)` with `χ² = 1`. If `f` agrees on `Re s > 1` with
the `L`-series of `χ` and is complex differentiable at a point `s ≠ 1` with `Re s = 1`, then
`f s ≠ 0`. -/
theorem ne_zero_of_eqOn_LSeries_galoisCharacterWeight_of_sq_eq_one (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ ^ 2 = 1) {f : ℂ → ℂ} {s : ℂ} (hs : s.re = 1) (hs1 : s ≠ 1)
    (hf : DifferentiableAt ℂ f s)
    (hfL : Set.EqOn f (LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction))
      {z | 1 < z.re}) :
    f s ≠ 0 := by
  -- The series of `χ² = 1` is the trivial one, which is differentiable at `2s - 1 ≠ 1`.
  obtain ⟨T, hT, hTL⟩ := exists_differentiableAt_eqOn_LSeries_galoisCharacterWeight_one K F
  have hs₂ : (2 * s - 1).re = 1 := by norm_num [hs]
  have hs₂1 : 2 * s - 1 ≠ 1 := fun h ↦ hs1 (by linear_combination h / 2)
  exact ne_zero_of_eqOn_LSeries_galoisCharacterWeight χ hs hf hfL (hT _ hs₂ hs₂1).continuousAt
    (by rwa [hχ])





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
# Nonvanishing of cyclotomic character series on the line `Re s = 1`

For a cyclotomic extension `F = K(μ_m)` of a number field `K` and a nontrivial character `χ` of
`Gal(F/K)`, the continued `L`-series `cyclotomicCharacterSeriesC K F χ` does not vanish anywhere
on the line `Re s = 1`. The series of the trivial character, which has a pole at `s = 1`, is
treated for every finite Galois extension in
`TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Nonvanishing`.

## Main results

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_of_re_eq_one`: for `F = K(μ_m)`
  and `χ ≠ 1`, the continued series of `χ` is nonzero on `Re s = 1`.
* `NumberField.Chebotarev.continuousOn_logDeriv_cyclotomicCharacterSeriesC`: for nontrivial
  characters, the logarithmic derivative is continuous on `Re s ≥ 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The case analysis on `χ²` follows Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`
  (Michael Stoll and David Loeffler), where `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`
  proves the analogous statement for Dirichlet `L`-functions.
-/

 section

open _root_.Complex _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.Topology

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

/-- **Nonvanishing on `Re s = 1`.** For `F = K(μ_m)` and a nontrivial character `χ` of
`Gal(F/K)`, the continued `L`-series of `χ` does not vanish at any `s` with `Re s = 1`. -/
theorem solution (m : ℕ) [_root_.NeZero m]
    [_root_.IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s.re = 1) : _root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC K F χ s ≠ 0 := by
  -- At `s = 1` this is the nonvanishing at the edge of the half-plane of convergence.
  obtain rfl | hs1 := _root_.eq_or_ne s 1
  · exact _root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_at_one K F m χ hχ
  -- The line `Re s = 1` lies in the half-plane `Re s > 1 - 1 / [K : ℚ]` of the continuations.
  have hdiff (ψ : (F ≃ₐ[K] F) →* ℂˣ) (hψ : ψ ≠ 1) {z : ℂ} (hz : z.re = 1) :
      _root_.DifferentiableAt ℂ (_root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC K F ψ) z :=
    (_root_.NumberField.Chebotarev.differentiableOn_cyclotomicCharacterSeriesC K F m ψ hψ).differentiableAt <|
      (_root_.isOpen_lt _root_.continuous_const _root_.Complex.continuous_re).mem_nhds <| by
        rw [_root_.Set.mem_ofPred_eq, hz]
        simpa only [_root_.Set.mem_ofPred_eq, hz] using
          _root_.TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hz.ge
  have hL (ψ : (F ≃ₐ[K] F) →* ℂˣ) : _root_.Set.EqOn (_root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC K F ψ)
      (_root_.LSeries (_root_.TauCeti.normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction)) {z | 1 < z.re} :=
    fun z hz ↦ _root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC_eq_LSeries K F ψ hz
  -- Away from `s = 1`, run the `3-4-1` argument; the series of `χ²` is continuous at `2s - 1`
  -- either as the trivial series (for `χ² = 1`) or as a continued nontrivial series.
  by_cases hχ2 : χ ^ 2 = 1
  · exact _root_.NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight_of_sq_eq_one χ hχ2 hs hs1
      (hdiff χ hχ hs) (hL χ)
  · exact _root_.NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight χ hs (hdiff χ hχ hs) (hL χ)
      (hdiff (χ ^ 2) hχ2 (by norm_num [hs])).continuousAt (hL (χ ^ 2))



end NumberField.Chebotarev

end
end
