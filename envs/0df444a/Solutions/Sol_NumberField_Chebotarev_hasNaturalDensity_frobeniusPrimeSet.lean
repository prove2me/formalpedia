-- Prove2me | solution 1 for NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:18:05.848205+00:00
-- url     : https://prove2.me/submissions/b9d21077-4c9c-408c-ab7c-9ef976c8948c

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_Analysis_SpecialFunctions_LogIntegral
import Definitions.Def_TauCeti_FieldTheory_Galois_FixedField
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_HigherPrimePowers
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NaturalDensity
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
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
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.LinearDisjoint
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
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Cyclotomic.Basic
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Northcott
import Mathlib.Probability.Distributions.Gaussian.Multivariate
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
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.PowerSeries.Log
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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.UniformSpace.UniformApproximation
import Theorems.Thm_AlgEquiv_zpowers_toFixedFieldAlgEquiv_eq_top
import Theorems.Thm_NumberField_Chebotarev_frobeniusPsi_asymptotic_of_isCyclotomicExtension
import Theorems.Thm_NumberField_Chebotarev_frobeniusPsi_asymptotic_of_mul_comm
import Theorems.Thm_NumberField_Chebotarev_frobeniusPsi_fixedField_asymptotic_iff
import Theorems.Thm_NumberField_Chebotarev_sum_frobeniusPrimePowerWeight
import Theorems.Thm_TauCeti_Real_tendsto_logIntegral_mul_log_div_atTop
import Theorems.Thm_TauCeti_primeCount_sub_mul_logIntegral_isLittleO
import Theorems.Thm_TauCeti_primePowerSummatory_indicator_sub_primeTheta
import Theorems.Thm_TauCeti_primePowerSummatory_isBigO_of_le_higherPrimePowerWeight
import Theorems.Thm_TauCeti_primePsi_le_ncard_mul_log
import Theorems.Thm_TauCeti_tendsto_primeCount_univ_atTop

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Inversion and powers of conjugacy classes, and the size of a class

Inversion of a group is compatible with conjugacy: `x` and `y` are conjugate exactly when `x⁻¹` and
`y⁻¹` are (`TauCeti.isConj_inv_iff`). So inversion descends to the conjugacy classes, where it is an
involution, recorded here as an `InvolutiveInv (ConjClasses G)` instance; `C⁻¹` is the class of the
inverses of the members of `C`, and it has the same size as `C`. A class fixed by this involution is
a **real** class (`TauCeti.IsRealClass`).

Powering likewise commutes with conjugation, so for a **monoid** `M` it too descends to the
conjugacy classes: `ConjClasses.pow C j`, written `C ^ j`, is the class of the `j`-th powers of
the members of `C`.

The other fact collected here is that the size of a conjugacy class is the index of the centralizer
of any of its members, and so divides the order of the group: the orbit-stabilizer theorem for the
conjugation action.

## Main statements

* `TauCeti.isConj_inv_iff`: conjugacy is inherited by inverses in both directions.
* `ConjClasses.inv_mk`: the inverse of the class of `g` is the class of `g⁻¹`.
* `TauCeti.IsRealClass`: a class containing an element conjugate to its own inverse, with
  `TauCeti.isRealClass_iff_inv_eq` identifying it with being fixed by inversion.
* `ConjClasses.ncard_carrier_inv` and `ConjClasses.card_carrier_inv`: a conjugacy
  class and its inverse have the same size, in `Set.ncard` and in `Nat.card` form.
* `ConjClasses.ncard_carrier_mk` and `ConjClasses.card_carrier_mk`: the size of a
  conjugacy class is the index of the centralizer of any of its members, in `Set.ncard` and in
  `Nat.card` form.
* `ConjClasses.ncard_carrier_mk_of_mem_center`: the class of a central element is a single
  point.
* `ConjClasses.card_carrier_mul_orderOf_dvd`: the class size times the order of a member
  divides the order of the group, so the quotient below is an exact ratio.
* `ConjClasses.card_div_card_carrier_mul_orderOf_pos`: for a finite group that ratio is positive.
* `ConjClasses.card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf`: that
  quotient equals the order of the centralizer divided by the order of the member.
* `ConjClasses.one_div_orderOf_div_card_div_card_carrier_mul_orderOf`: dividing `1 / orderOf σ`
  by that quotient, in a semifield of characteristic zero, leaves `#C / #G`.
* `ConjClasses.ncard_carrier_mk_eq_card_filter` and
  `ConjClasses.card_carrier_mk_eq_card_filter`: the size of a conjugacy class as the
  cardinality of a `Finset`, which makes it computable.
* `ConjClasses.card_carrier_dvd_card`: the size of a conjugacy class divides the order of
  the group, with `ConjClasses.card_carrier_cast_ne_zero` the consequence that the size of
  a class is nonzero in any semiring where the group order is, and
  `ConjClasses.card_carrier_div_card_ne_zero` the nonvanishing of `#C / #G` for a finite group.
* `ConjClasses.pow`: the power operation itself, with `C ^ j` its notation.
* `ConjClasses.mem_pow_iff`: an element lies in `C ^ j` exactly when it is a
  `j`-th power of a member of `C`, with `ConjClasses.mk_pow` the computation rule.
* `ConjClasses.pow_zero`, `ConjClasses.pow_one` and
  `ConjClasses.pow_mul`: the identity and composition laws for that power.
* `ConjClasses.map_mk`: the computation rule for `ConjClasses.map` on representatives,
  with `ConjClasses.map_pow` the consequence that the power is natural in the monoid.
* `ConjClasses.mk_ne_mk_of_orderOf_ne`: elements of different orders lie in different conjugacy
  classes.

## Implementation notes

The inversion is an instance rather than a plain function so that the notation `C⁻¹`, the
involutivity lemma `inv_inv` and the reindexing equivalence `Equiv.inv` are all available for
conjugacy classes. Powering is instead a named definition `ConjClasses.pow` with a `Pow` instance
delegating to it, so that the roadmap's `C.pow j` and the notation `C ^ j` are the same function;
the lemmas below are all stated in the `^` form. There is still no
multiplication on `ConjClasses M` — `Pow (ConjClasses M) ℕ` is a bare power operation, not the
`npow` field of a monoid structure, and none of the lemmas here presuppose one.

The power operation is developed for the Chebotarev roadmap (`Chebotarev/README.md` Layer 1,
"consumed Frobenius classes and powers of conjugacy classes", whose `Suggested.lean` pins these
signatures); its consumer there is the von Mangoldt fibre, which sums over the classes `C ^ j`.
That is also why a `pow_two_cyclicFour` regression is kept: a group of
exponent two has no proper nonidentity square, so it cannot separate a correct power operation
from one that collapses to the identity. It is `private`, being a check on this development
rather than reusable conjugacy-class API. This operation is *not* adapted from the
Birkbeck–Brasca `chebotarev-density` development, which works with `ConjClasses.mk` and
`Subgroup.zpowers` directly and never forms `C ^ j`.

The two arithmetic statements concern the quotient `#G / (#C * orderOf σ)`. The first says the
division is exact — `#C` is the index of the centralizer of `σ`, and `orderOf σ` divides that
centralizer's order, so their product divides `#G` — and the second evaluates the quotient as the
centralizer's order over `orderOf σ`. Neither asserts that either side counts anything; a caller
wanting a cardinality interpretation must supply it.
-/

 section

namespace TauCeti

variable {G : Type*} [Group G]





end TauCeti

namespace ConjClasses

variable {G : Type*} [Group G]











/-- **The size of a conjugacy class is the index of the centralizer of any of its members.** The
class is the orbit of `g` under the conjugation action and the centralizer is the stabilizer, so
this is the orbit-stabilizer theorem. -/
theorem ncard_carrier_mk (g : G) :
    (ConjClasses.mk g).carrier.ncard = (Subgroup.centralizer {g}).index := by
  rw [← ConjAct.orbit_eq_carrier_conjClasses, ← MulAction.index_stabilizer,
    Subgroup.centralizer_eq_comap_stabilizer]
  exact ((MulAction.stabilizer (ConjAct G) g).index_comap_of_surjective
    (f := ConjAct.toConjAct.toMonoidHom) ConjAct.toConjAct.surjective).symm



/-- **The size of a conjugacy class is the index of the centralizer of any of its members**, in
`Nat.card` form.

Not `@[simp]`: Mathlib's `Nat.card_coe_set_eq` is itself `simp`, so the left-hand side simplifies
to `(ConjClasses.mk g).carrier.ncard` and the simp normal form linter rejects the pair; that
normalized form is `ConjClasses.ncard_carrier_mk`. -/
theorem card_carrier_mk (g : G) :
    Nat.card (ConjClasses.mk g).carrier = (Subgroup.centralizer {g}).index := by
  rw [Nat.card_coe_set_eq, ncard_carrier_mk]











end ConjClasses

namespace TauCeti

variable {G : Type*} [Group G]





-- Not a `simp` lemma: `isRealClass_iff_inv_eq` and `ConjClasses.inv_mk` already rewrite the
-- left-hand side to `ConjClasses.mk g⁻¹ = ConjClasses.mk g`, so tagging it makes `simpNF` fail.


end TauCeti

/-! ### The size of a class against the order of a member -/

namespace ConjClasses

-- Source. Both statements are specified by the Chebotarev roadmap. The divisibility is the
-- declaration pinned at `TauCetiRoadmap/Chebotarev/Suggested.lean` lines 377-382, there stated
-- with `[Finite G]`. The quotient identity is `TauCetiRoadmap/Chebotarev/README.md` §8.2, which
-- writes it `#G / (#C * f) = #Centralizer_G(σ) / f` for `f = orderOf σ` and asks for
-- `#C * f ∣ #G` as a separate statement.

/-- **The size of a conjugacy class times the order of a member divides the order of the group.**

For a *finite* group this is what makes `Nat.card G / (Nat.card C.carrier * orderOf σ)` an exact
ratio rather than a truncated division, which
`card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf` then evaluates. No finiteness
is assumed here: for an infinite group `Nat.card G` is `0`, and every natural number divides `0`. -/
theorem card_carrier_mul_orderOf_dvd {G : Type*} [Group G] (C : ConjClasses G) (σ : G)
    (hσ : σ ∈ C.carrier) :
    Nat.card C.carrier * orderOf σ ∣ Nat.card G := by
  rw [mem_carrier_iff_mk_eq] at hσ
  subst hσ
  obtain ⟨k, hk⟩ := (Subgroup.centralizer {σ}).orderOf_dvd_natCard
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  exact ⟨k, by rw [ConjClasses.card_carrier_mk, mul_assoc, ← hk, Subgroup.index_mul_card]⟩





/-- **Dividing `1 / orderOf σ` by that quotient leaves `#C / #G`.** Since
`#C.carrier * orderOf σ` divides `#G`, the quotient casts to the exact ratio, and in a semifield of
characteristic zero `(1 / orderOf σ) / (#G / (#C.carrier * orderOf σ)) = #C.carrier / #G`.
For infinite groups both sides vanish because `Nat.card G = 0`. -/
theorem one_div_orderOf_div_card_div_card_carrier_mul_orderOf {G : Type*} [Group G]
    {K : Type*} [Semifield K] [CharZero K] (C : ConjClasses G) (σ : G) (hσ : σ ∈ C.carrier) :
    (1 / orderOf σ : K) / ((Nat.card G / (Nat.card C.carrier * orderOf σ) : ℕ) : K) =
      Nat.card C.carrier / Nat.card G := by
  cases finite_or_infinite G with
  | inl h =>
      have : Nonempty C.carrier := ⟨⟨σ, hσ⟩⟩
      have hC : (Nat.card C.carrier : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      have hord : (orderOf σ : K) ≠ 0 := Nat.cast_ne_zero.mpr (orderOf_pos σ).ne'
      rw [Nat.cast_div (C.card_carrier_mul_orderOf_dvd σ hσ)
        (by push_cast; exact mul_ne_zero hC hord)]
      push_cast
      rw [div_div_eq_mul_div, one_div_mul_eq_div, mul_div_cancel_right₀ _ hord]
  | inr h => simp [Nat.card_eq_zero_of_infinite]

end ConjClasses

/-! ### Powers of a conjugacy class -/

namespace ConjClasses

variable {M : Type*} [Monoid M]





/-- The `j`-th power of the class of `a` is the class of `a ^ j`. -/
@[simp]
theorem mk_pow (a : M) (j : ℕ) : ConjClasses.mk a ^ j = ConjClasses.mk (a ^ j) := by
  -- `pow` is sealed, so this is no longer `rfl`: a theorem exported from this module may only
  -- unfold exposed definitions. Go through `pow`'s equation lemma, after which the statement is
  -- exactly `Quotient`'s computation rule for `Quotient.map`.
  change ConjClasses.pow (ConjClasses.mk a) j = ConjClasses.mk (a ^ j)
  rw [ConjClasses.pow]
  exact Quotient.map_mk _ _ _





/-- The first power of a conjugacy class is the class itself. -/
@[simp]
theorem pow_one (C : ConjClasses M) : C ^ 1 = C := by
  obtain ⟨a, rfl⟩ := ConjClasses.exists_rep C
  rw [mk_pow, _root_.pow_one]











end ConjClasses

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
# The logarithmic integral

This file defines the offset logarithmic integral `Li x = ∫ t in 2..x, (log t)⁻¹` and proves the
prime-number-theorem normalisation `Li x ~ x / log x` as `x → ∞`.

The lower endpoint is `2` rather than `0`: the integrand has a nonintegrable singularity at
`t = 1`, so the unshifted `li` exists only as a principal value, while every arithmetic
application compares a prime count with `Li`. The endpoint agrees with the one used by the
partial-summation identities for prime counts, so the two can be combined without a shift of
origin.

The asymptotic is proved from the exact identity
`Li x = x / log x - 2 / log 2 + ∫ t in 2..x, ((log t) ^ 2)⁻¹`,
the fundamental theorem of calculus applied to `t ↦ t / log t`, together with the estimate that
the remaining integral is `o (x / log x)`. Splitting that integral at `√x` bounds it by
`√x / (log 2) ^ 2 + 4 * x / (log x) ^ 2`, and both terms are `o (x / log x)`.

## Main declarations

* `TauCeti.Real.logIntegral` — the offset logarithmic integral.
* `TauCeti.Real.le_logIntegral` — the elementary lower bound `(x - 2) / log x ≤ Li x`.
* `TauCeti.Real.logIntegral_eq_div_log_sub_add` — the antiderivative identity above.
* `TauCeti.Real.logIntegral_isEquivalent_div_log` — `Li x ~ x / log x` at infinity, with the
  quotient form `TauCeti.Real.tendsto_logIntegral_mul_log_div_atTop`.
* `TauCeti.Real.tendsto_div_div_log_of_isLittleO_logIntegral` — an `o (x / log x)` error
  relative to `δ Li x` gives `f x / (x / log x) → δ`.
* `TauCeti.Real.isLittleO_integral_div_mul_log_sq` — for `f` interval integrable above `2` and of
  at most linear growth, `∫ t in 2..x, f t / (t * log t ^ 2)` is `o (x / log x)`.

The auxiliary bounds `TauCeti.Real.integral_inv_log_pow_le` and
`TauCeti.Real.le_integral_inv_log_pow` estimate `∫ t in a..b, ((log t) ^ n)⁻¹` by monotonicity of
the logarithm. They are stated for a general exponent because the identity above needs `n = 2`
while `Li` itself is the case `n = 1`.

## Roadmap role

This is the analytic half of Layer **6.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`,
which asks for `Li` together with `Li(x) ∼ x/log x` on the way to the transfer
`ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)` that Layer 10.3 exports as `primeCount_asymptotic_of_primeTheta`.
The weighted-remainder estimate `isLittleO_integral_div_mul_log_sq` is the analytic input to that
transfer: it is what absorbs the integral produced by Abel summation.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.

Mathlib's `Mathlib/NumberTheory/Chebyshev.lean` carries out this estimate for the rational
Chebyshev function, in `Chebyshev.integral_theta_div_log_sq_isLittleO`; the argument for a general
integrand below follows the same split into a bounded initial segment and a linearly bounded tail.
-/

 section

namespace TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology

/-! ### Reciprocal powers of the logarithm -/











/-! ### The logarithmic integral -/











/-! ### The asymptotic `Li x ~ x / log x` -/











/-- **`Li x` is asymptotically equivalent to `x / log x`.** -/
theorem logIntegral_isEquivalent_div_log :
    logIntegral ~[atTop] fun x : ℝ ↦ x / Real.log x := by
  refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  · refine tendsto_logIntegral_mul_log_div_atTop.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x _
    rw [Pi.div_apply, div_div_eq_mul_div]

/-! ### A weighted remainder integral

The integral `∫ t in 2..x, f t / (t * log t ^ 2)` is what Abel summation leaves behind when a
logarithmically weighted counting function is converted into an unweighted one.  It is negligible
on the scale `x / log x` as soon as `f` grows at most linearly. -/















end TauCeti.Real

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
# Fixed fields and fixing subgroups

Complements to Mathlib's Galois correspondence: its interaction with the complete-lattice
operations, when a fixed field and an intermediate field generate the whole extension, when the
correspondence survives dropping finiteness of `M / K` for a finite subgroup, and what the
correspondence gives for a cyclic subgroup.

Taking fixed fields always sends joins of automorphism subgroups to intersections of intermediate
fields. For a finite Galois extension it also sends subgroup intersections to composita of fixed
fields. Both the binary and indexed forms are recorded so that finite generating families and
arbitrary families can use these lattice laws without manually passing through the order dual in
the Galois correspondence.

For a finite Galois extension `M / K`, a subgroup `H ≤ Gal(M/K)` and an intermediate field `E`,
the fixed field of `H` and `E` generate `M` exactly when `H` meets the fixers of `E` trivially.
With no hypothesis on `M / K`, the fixers of an arbitrary join of intermediate fields are the
automorphisms fixing each of them.

The correspondence is equivariant for conjugation: the fixed field of a conjugate subgroup is the
image of the fixed field under the conjugating automorphism.

The correspondence between subgroups and their fixed fields also holds with no hypothesis on
`M / K` at all, provided the subgroup is finite: Artin's theorem makes `M` finite Galois over the
fixed field of a finite `H`, and the fixers of that field are then exactly `H`. This is how a
subgroup of the automorphism group of an infinite extension is recovered from the field it cuts
out; the fixing subgroup of a subfield of finite degree is finite for the same reason.

The last results specialise the correspondence to a *cyclic* subgroup: the field fixed by a finite
cyclic group of automorphisms has `M` cyclic over it, and for `⟨σ⟩` there is a named automorphism
over the fixed field — `AlgEquiv.toFixedFieldAlgEquiv σ` acts on `M` as `σ` does, and generates
once `⟨σ⟩` is finite.

Neither `M / K` Galois nor `M / K` finite is needed, and neither is faithfulness of the action:
`FixedPoints.toAlgAut_surjective` asks only that the group be finite, and cyclicity passes along
its surjection. The fixed-point subfield it produces is the one underlying
`IntermediateField.fixedField`.

A simple extension `K⟮x⟯` is fixed pointwise by exactly those automorphisms that fix `x`, so
its fixing subgroup is the stabilizer of `x`; this too needs no hypothesis on `M / K` at all.

Two facts hold for every intermediate field `E` algebraic over `K`, with no separability anywhere
and nothing asked of `M / K`: its fixing subgroup is closed in the Krull topology, being the
intersection over the finite simple subextensions of their open fixing subgroups; and it is
unchanged by cutting `E` down to its part inside `separableClosure K M`, because every element of
`E` has a `q`-th power iterate there. The second is why a Galois correspondence over an
inseparable extension can only be indexed by the intermediate fields of the separable closure.

## Main results

* `Subgroup.fixedField_inf` and `Subgroup.fixedField_sup`
* `Subgroup.fixedField_iInf` and `Subgroup.fixedField_iSup`
* `Subgroup.fixedField_sup_eq_top_iff`
* `Subgroup.fixedField_map_conj`
* `IntermediateField.fixingSubgroup_inf`
* `IntermediateField.fixingSubgroup_iSup`
* `IntermediateField.fixingSubgroup_isClosed_of_isAlgebraic`
* `IntermediateField.fixingSubgroup_inf_separableClosure`
* `IntermediateField.fixingSubgroup_fixedField_of_finite`
* `IntermediateField.finite_of_finiteDimensional_fixedField`
* `IntermediateField.card_fixingSubgroup_le`
* `IntermediateField.fixingSubgroup_adjoin_simple`, with
  `IntermediateField.mem_fixedField_stabilizer`,
  `IntermediateField.fixedField_stabilizer_eq_adjoin_simple`,
  `IntermediateField.fixedField_iInf_stabilizer_eq_adjoin_range` and
  `IntermediateField.adjoin_eq_top_of_fixedField_stabilizer`: the stabilizer of `x` fixes
  exactly `K⟮x⟯`, in which `x` is a primitive element
* `FixedPoints.isCyclic_algEquiv`
* `AlgEquiv.toFixedFieldAlgEquiv`, with `AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top` and
  `AlgEquiv.card_algEquiv_fixedField_zpowers`
* `TauCeti.natCard_algEquiv_dvd_finrank`: the automorphism group of a finite extension has order
  dividing the degree, since that order is the degree over the field fixed by all automorphisms
-/

 section

open IntermediateField

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]







end IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]











end Subgroup

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

















-- The subgroup extensionality argument below, reducing membership of `K⟮x⟯.fixingSubgroup` to
-- `IntermediateField.forall_mem_adjoin_smul_eq_self_iff` at the singleton `{x}`, is adapted from
-- the proof of `stabilizer_isOpen_of_isIntegral` in `Mathlib/FieldTheory/KrullTopology.lean`,
-- which uses it there to identify a point stabilizer with the fixing subgroup of a finite
-- intermediate field. Here it is recorded as a statement in its own right, with no integrality
-- hypothesis.










end IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]



end Subgroup

namespace FixedPoints



end FixedPoints

namespace AlgEquiv

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

-- Source. The fixed field of `⟨σ⟩` and its named generator are the constructions pinned at
-- `TauCetiRoadmap/Chebotarev/Suggested.lean` lines 283-291, as `cyclicFixedField` and
-- `fixedFieldGenerator`. Neither name is kept: the field is spelled
-- `IntermediateField.fixedField (Subgroup.zpowers σ)` throughout rather than abbreviated, and the
-- automorphism is `toFixedFieldAlgEquiv`, because it is defined without finiteness and only
-- generates once `⟨σ⟩` is finite.



/-- **The rebundled automorphism acts as `σ`.** This is what makes `toFixedFieldAlgEquiv σ`
usable: it is a different bundling of the same underlying map, over the fixed field rather than
over `K`. It says nothing about generation, which needs `⟨σ⟩` finite and is
`zpowers_toFixedFieldAlgEquiv_eq_top`. -/
@[simp]
theorem toFixedFieldAlgEquiv_apply (σ : M ≃ₐ[K] M) (x : M) :
    toFixedFieldAlgEquiv σ x = σ x :=
  (rfl)

/-- **Restricting scalars undoes the rebundling.** Read back over `K`, `σ.toFixedFieldAlgEquiv`
is `σ` itself — the elimination rule matching `toFixedFieldAlgEquiv_apply`, in bundled form, which
is what a tower argument needs when it must produce an equation between automorphisms rather than
between their values. -/
@[simp]
theorem restrictScalars_toFixedFieldAlgEquiv (σ : M ≃ₐ[K] M) :
    AlgEquiv.restrictScalars K σ.toFixedFieldAlgEquiv = σ :=
  AlgEquiv.ext fun x ↦ toFixedFieldAlgEquiv_apply σ x



/-- **The automorphism group of `M` over `M ^ ⟨σ⟩` has order `orderOf σ`.** The automorphisms of
`M` fixing the field cut out by `⟨σ⟩` number exactly the order of `σ`.

Only the generated subgroup `⟨σ⟩` need be finite: `M / K` is asked to be neither finite nor
Galois, so this applies to an automorphism of finite order of an arbitrary extension. -/
-- Not a `simp` lemma: `simpNF` rejects it. Normalising the left-hand side sends `simp` after
-- `Fintype Gal(M/M ^ ⟨σ⟩)`, and with only `Finite (Subgroup.zpowers σ)` in scope that instance
-- search exhausts its heartbeat budget instead of failing, so the lemma could never fire.
theorem card_algEquiv_fixedField_zpowers (σ : M ≃ₐ[K] M) [Finite (Subgroup.zpowers σ)] :
    Nat.card (M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] M) = orderOf σ := by
  have horder : orderOf (toFixedFieldAlgEquiv σ) = orderOf σ := by
    rw [← orderOf_injective (AlgEquiv.restrictScalarsHom K)
      (AlgEquiv.restrictScalarsHom_injective K) (toFixedFieldAlgEquiv σ),
      AlgEquiv.restrictScalarsHom_apply, restrictScalars_toFixedFieldAlgEquiv]
  rw [← Subgroup.card_top (G := M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] M),
    ← zpowers_toFixedFieldAlgEquiv_eq_top σ, Nat.card_zpowers, horder]

end AlgEquiv

namespace TauCeti



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























/-! ### Generic summatory functions -/



/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]















/-- The summatory function of a pointwise nonnegative real weight is nonnegative. -/
theorem summatory_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (x : ℝ) : 0 ≤ summatory N w x :=
  Finset.sum_nonneg fun i _ ↦ hw i













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

























/-- A prime-power ideal has exponent one exactly when it is itself prime. -/
@[simp] theorem primePowerExponent_eq_one_iff (A : IdealPrimePower K) :
    primePowerExponent A = 1 ↔ Prime (A : Ideal (𝓞 K)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ primePowerExponent_eq h (pow_one _)⟩
  rw [← primePowerBase_pow_primePowerExponent A, h, pow_one]
  exact prime_primePowerBase A

/-- A prime-power ideal which is not prime has exponent at least two. -/
theorem two_le_primePowerExponent {A : IdealPrimePower K} (hA : ¬ Prime (A : Ideal (𝓞 K))) :
    2 ≤ primePowerExponent A := by
  have h₁ := primePowerExponent_pos A
  have h₂ : primePowerExponent A ≠ 1 := fun h ↦ hA ((primePowerExponent_eq_one_iff A).mp h)
  omega





/-- The underlying ideal of a height-one prime is prime. -/
theorem IdealPrimePower.prime_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    Prime ((IdealPrimePower.ofPrime v : IdealPrimePower K) : Ideal (𝓞 K)) :=
  Ideal.prime_of_isPrime v.ne_bot v.isPrime

/-- A height-one prime is its own prime base. -/
@[simp]
theorem primePowerBase_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    primePowerBase (IdealPrimePower.ofPrime v) = v :=
  HeightOneSpectrum.ext
    (primePowerBase_asIdeal_eq (IdealPrimePower.prime_ofPrime v) (pow_one _))

/-- A height-one prime has exponent one as a prime-power ideal. -/
@[simp]
theorem primePowerExponent_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    primePowerExponent (IdealPrimePower.ofPrime v) = 1 :=
  primePowerExponent_eq (IdealPrimePower.prime_ofPrime v) (pow_one _)





















variable (K)

/-! ### Summatory functions over ideals and over primes -/











/-- A prime summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem primeSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : HeightOneSpectrum (𝓞 K) → M) (x : ℝ) :
    primeSummatory K w x = ∑ v ∈ primesLE K x, w v :=
  summatory_apply _ w x

/-- A prime-power summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem primePowerSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : IdealPrimePower K → M) (x : ℝ) :
    primePowerSummatory K w x = ∑ A ∈ primePowersLE K x, w A :=
  summatory_apply _ w x







/-- A pointwise nonnegative real weight has a nonnegative prime-power summatory function. -/
theorem primePowerSummatory_nonneg (w : IdealPrimePower K → ℝ) (hw : ∀ A, 0 ≤ w A) (x : ℝ) :
    0 ≤ primePowerSummatory K w x :=
  summatory_nonneg _ hw x











variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)









/-! ### The weighted prime counts -/





variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}



/-- The unweighted prime count as an explicit sum over the inclusive carrier. -/
theorem primeCount_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = ∑ v ∈ primesLE K x, S.indicator 1 v := by
  rw [primeCount, primeSummatory_apply]

/-- The count of `S` really is the cardinality of the set of primes of `S` below the cutoff. -/
theorem primeCount_eq_card (S : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ S)] (x : ℝ) :
    primeCount K S x = ((primesLE K x).filter (· ∈ S)).card := by
  rw [primeCount_apply]
  simp [Set.indicator_apply, Finset.sum_boole]









/-- The logarithm of the absolute norm of a height-one prime is positive. -/
theorem log_absNorm_asIdeal_pos (v : HeightOneSpectrum (𝓞 K)) :
    0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
  Real.log_pos (by linarith [two_le_absNorm_asIdeal_real v])









































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
# Crude prime counts and the higher prime powers of a number field

Chebyshev's `ψ` counts every prime power `𝔭 ^ k` with the logarithmic weight `log N(𝔭)`, while
`ϑ` counts only the primes themselves.  Their difference is the sum of `log N(𝔭)` over the
*higher* prime powers, those with `k ≥ 2`, and the point of this file is that this difference is
negligible: it is `O(√x log² x)`, hence `o(x)`.

Two elementary counting bounds carry the argument.

* `TauCeti.two_pow_card_le_absNorm`: distinct primes dividing a nonzero ideal `I` each contribute
  a factor of at least `2` to `N(I)`, so there are at most `log₂ N(I)` of them.
* `TauCeti.card_primesLE_mul_log_two_le`: every prime of norm at most `x` divides the principal
  ideal generated by `⌊x⌋₊ !`, whose absolute norm is `(⌊x⌋₊ !) ^ [K:ℚ]`.  Feeding that into the
  previous bound gives `π_K(x) ≤ [K:ℚ] / log 2 · x log x`.

Neither bound is sharp — the true order of `π_K(x)` is `x / log x` — but they are proved from
scratch, with no analytic input and an explicit constant, and they are strong enough for every
estimate below.  The repository's existing effective count
`NumberField.card_ideal_absNorm_le`, which bounds the number of nonzero ideals of norm at most `X`
by `X² · 2 ^ [K:ℚ]`, is not: being quadratic it only gives `π_K(√x) = O(x)`, which loses the
saving that makes the higher prime powers negligible.

The higher prime powers are then summed by fibring over the prime base: for a fixed prime `𝔭`,
the exponents `k ≥ 2` with `N(𝔭) ^ k ≤ x` number at most `log x / log N(𝔭)`, so the whole fibre
contributes at most `log x`.  Since a higher prime power of norm at most `x` has
`N(𝔭) ^ 2 ≤ x`, only the primes of norm at most `√x` occur, and the total is at most
`π_K(√x) · log x`.

## Main definitions

* `TauCeti.higherPrimePowerWeight` is the standard logarithmic prime-power weight `log N(𝔭)`,
  restricted to the prime powers `𝔭 ^ k` with `k ≥ 2` and set to zero on the primes themselves.
* `TauCeti.higherPrimePowerTheta` is its inclusive summatory function, that is, `ψ - ϑ`.

## Main results

* `TauCeti.primeCount_le_mul_log` and `TauCeti.primeCount_isBigO`: the crude prime count.
* `TauCeti.higherPrimePowerTheta_le`: the explicit bound
  `ψ(x) - ϑ(x) ≤ [K:ℚ] / (2 log 2) · √x log² x`.
* `TauCeti.higherPrimePowerTheta_isBigO` and `TauCeti.higherPrimePowerTheta_isLittleO`: the
  `O(√x log² x)` and `o(x)` forms.
* `TauCeti.primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight`: the same conclusion for
  any normed additive-group-valued prime-power weight whose norm is dominated by a constant
  multiple of the standard one.  This isolates exactly the hypothesis another arithmetic weight
  has to supply.
* `TauCeti.primePowerSummatory_indicator_isLittleO`: its specialization to the higher prime powers
  whose base lies in a prescribed set of primes.

## Roadmap role

This is the prime and prime-power half of Layer **5.1** together with Layer **5.2** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, whose target 5.2 asks for "the generic
`O(√x log² x)` estimate under the standard logarithmic prime-power weight" and for the
hypotheses needed by other arithmetic weights.  Layer 10.2 consumes it as the named estimate
turning an asymptotic for `ψ` into one for `ϑ`; the roadmap's own accounting there requires only
the `o(x)` corollary.

The ideal-counting half of Layer 5.1 is a separate estimate: it is analytic, resting on Mathlib's
`NumberField.Ideal.tendsto_norm_le_div_atTop₀`, and is not needed here.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 7.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open _root_.Filter _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-! ### Counting the primes below a cutoff -/











/-! ### The standard logarithmic weight on the higher prime powers -/



/-- On a higher prime power, the standard weight is the logarithm of the norm of the base. -/
@[simp] theorem higherPrimePowerWeight_of_two_le_primePowerExponent {A : IdealPrimePower K}
    (hA : 2 ≤ primePowerExponent A) :
    higherPrimePowerWeight A = Real.log (Ideal.absNorm (primePowerBase A).asIdeal) :=
  if_pos hA

/-- On a prime, the standard weight vanishes. -/
@[simp] theorem higherPrimePowerWeight_of_prime {A : IdealPrimePower K}
    (hA : Prime (A : Ideal (𝓞 K))) : higherPrimePowerWeight A = 0 := by
  have hexp : primePowerExponent A = 1 := (primePowerExponent_eq_one_iff A).mpr hA
  exact if_neg (by omega)

/-- The higher-prime-power weight is nonnegative. -/
theorem higherPrimePowerWeight_nonneg (A : IdealPrimePower K) : 0 ≤ higherPrimePowerWeight A := by
  by_cases hA : Prime (A : Ideal (𝓞 K))
  · exact (higherPrimePowerWeight_of_prime hA).ge
  · rw [higherPrimePowerWeight_of_two_le_primePowerExponent (two_le_primePowerExponent hA)]
    exact Real.log_nonneg (by linarith [two_le_absNorm_asIdeal_real (primePowerBase A)])













/-! ### The `O(√x log² x)` estimate -/







/-- `√x log² x` is `o(x)`: this is what makes the higher prime powers negligible for the
prime-number-theorem transfer of Layer 10.2. -/
theorem isLittleO_sqrt_mul_log_sq :
    (fun x : ℝ ↦ Real.sqrt x * Real.log x ^ 2) =o[atTop] fun x : ℝ ↦ x := by
  have h1 : (fun x : ℝ ↦ Real.log x ^ 2) =o[atTop] fun x : ℝ ↦ Real.sqrt x := by
    refine (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ) < 1 / 2)).congr' ?_ ?_
    · filter_upwards with x
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    · filter_upwards with x
      rw [Real.sqrt_eq_rpow]
  refine ((Asymptotics.isBigO_refl (fun x : ℝ ↦ Real.sqrt x) atTop).mul_isLittleO h1).congr'
    EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact Real.mul_self_sqrt hx



/-! ### Other arithmetic weights -/



/-- Any normed additive-group-valued prime-power weight whose norm is dominated by a constant
multiple of the standard logarithmic weight on the higher prime powers has `o(x)` summatory
function. -/
theorem primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight
    (K : Type*) [Field K] [NumberField K] {E : Type*} [NormedAddCommGroup E]
    {w : IdealPrimePower K → E} {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ A, ‖w A‖ ≤ C * higherPrimePowerWeight A) :
    (fun x ↦ primePowerSummatory K w x) =o[atTop] fun x : ℝ ↦ x :=
  (primePowerSummatory_isBigO_of_le_higherPrimePowerWeight K hC hw).trans_isLittleO
    isLittleO_sqrt_mul_log_sq

/-- Restricting to the prime powers whose base lies in a set `S` of primes only removes
nonnegative terms, so the `o(x)` estimate survives.  This is the form Layer 10.2 consumes when it
removes the higher prime powers from `ψ` over a prime set. -/
theorem primePowerSummatory_indicator_isLittleO (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    (fun x ↦ primePowerSummatory K
        ({A : IdealPrimePower K | primePowerBase A ∈ S}.indicator higherPrimePowerWeight) x)
      =o[atTop] fun x : ℝ ↦ x :=
  primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight K zero_le_one
    fun A ↦ by
      rw [norm_indicator_eq_indicator_norm, one_mul]
      exact Set.indicator_apply_le'
        (fun _ ↦ le_of_eq (Real.norm_of_nonneg (higherPrimePowerWeight_nonneg A)))
        fun _ ↦ higherPrimePowerWeight_nonneg A

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
# Natural density of sets of prime ideals

For a number field `K`, this file defines the natural density of a set `S` of nonzero prime
ideals as the limit

```text
  primeCount K S x / primeCount K Set.univ x
```

as the inclusive real cutoff `x` tends to infinity. This normalization matches Mathlib's
ratio-normalized `NumberField.Set.HasDirichletDensity`: a density is measured relative to all
prime ideals of the same number field, rather than relative to an external approximation such as
`x / log x`.

The denominator really tends to infinity. Indeed, lying over supplies a prime of `𝓞 K` above
every rational prime, so the height-one spectrum is infinite. Its bounded-norm subsets are finite
and exhaust the spectrum, whence their cardinalities tend to infinity. This fact both makes the
whole spectrum have density one and ensures that a fixed finite error disappears in the ratio.

## Main results

* `NumberField.Set.HasNaturalDensity`: ratio-normalized natural density for a set of prime ideals.
* `NumberField.Set.hasNaturalDensity_def`: the defining ratio-convergence characterization.
* `NumberField.Set.HasNaturalDensity.union`,
  `NumberField.Set.hasNaturalDensity_biUnion_finset` and
  `NumberField.Set.HasNaturalDensity.compl`: finite Boolean calculus for natural density.
* `NumberField.Set.HasNaturalDensity.of_finite_symmDiff`: changing a prime set on finitely many
  primes preserves its natural density.
* `NumberField.Set.hasNaturalDensity_of_finite`: every finite set of prime ideals has natural
  density zero.
* `NumberField.Set.hasNaturalDensity_of_isLittleO_logIntegral`: if all primes satisfy
  `π(x) = Li(x) + o(x / log x)` and the primes of `S` satisfy `π_S(x) = δ Li(x) + o(x / log x)`,
  then `S` has natural density `δ`.
* `NumberField.Set.isUpperDirichletDensityBound_of_eventually_primeCount_le` and
  `NumberField.Set.isLowerDirichletDensityBound_of_eventually_le_primeCount`: an eventual
  one-sided bound on the proportion of primes of `S` below `x` is the same one-sided bound for
  Dirichlet density.
* `NumberField.Set.hasDirichletDensity_of_hasNaturalDensity`: natural density implies Dirichlet
  density, with the same value.

The comparison with Dirichlet density rests on two inputs. Abel summation against the decreasing
function `t ↦ t ^ (-s)` (`TauCeti.tsum_mul_le_of_summatory_le`) turns an eventual bound
`π_S(x) ≤ c · π(x)` into a bound `P_S(s) ≤ c · P(s) + C` with `C` independent of `s > 1`, where
`P_S` is Mathlib's `NumberField.Set.primeIdealZetaSum S`. The all-prime sum `P(s)` tends to
infinity as `s → 1⁺` (`TauCeti.tendsto_primeIdealZetaSum_univ_atTop`), so the constant `C`
disappears from the ratio `P_S(s) / P(s)`.

The definition, its elementary calculus, and the comparison with Dirichlet density are standard;
see J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4, J.-P. Serre, *Corps locaux*, Chapter
VI, or J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

 section

namespace NumberField.Set

open _root_.Filter _root_.IsDedekindDomain
open scoped _root_.NumberField _root_.Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}



/-- Unfolds `HasNaturalDensity` to the convergence of the ratio of prime counts. -/
theorem hasNaturalDensity_def :
    HasNaturalDensity S δ ↔ Tendsto (fun x : ℝ => TauCeti.primeCount K S x /
      TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 δ) :=
  (Iff.rfl)



























/-! ### Natural density implies Dirichlet density -/















open Asymptotics in
/-- **Natural density from prime-counting asymptotics.** If the primes of `K` satisfy
`π(x) = Li(x) + o(x / log x)` and the primes of `S` satisfy `π_S(x) = δ Li(x) + o(x / log x)`,
then `S` has natural density `δ`. -/
theorem hasNaturalDensity_of_isLittleO_logIntegral
    (hS : (fun x ↦ TauCeti.primeCount K S x - δ * TauCeti.Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x)
    (hU : (fun x ↦ TauCeti.primeCount K Set.univ x - TauCeti.Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x) : HasNaturalDensity S δ := by
  have hdiff : (fun x ↦ TauCeti.primeCount K S x - δ * TauCeti.primeCount K Set.univ x)
      =o[atTop] fun x : ℝ ↦ x / Real.log x :=
    (hS.sub (hU.const_mul_left δ)).congr_left fun x ↦ by ring
  have hequiv : TauCeti.primeCount K Set.univ ~[atTop] fun x : ℝ ↦ x / Real.log x :=
    (hU.add TauCeti.Real.logIntegral_isEquivalent_div_log).congr_left fun x ↦ by simp
  -- `π_S / π - δ = (π_S - δ π) / π → 0`
  refine hasNaturalDensity_def.mpr <| (zero_add δ ▸
    (hdiff.trans_isBigO hequiv.isBigO_symm).tendsto_div_nhds_zero.add_const δ).congr' ?_
  filter_upwards [(TauCeti.tendsto_primeCount_univ_atTop K).eventually_gt_atTop 0] with x hx
  grind

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
# Chebyshev's `ψ` for a set of prime ideals, and the removal of the higher prime powers

For a set `S` of height-one primes of the ring of integers of a number field `K`, Chebyshev's
`ψ` weights *every* prime power `𝔭 ^ k` with `𝔭 ∈ S` and `k ≥ 1` by `log N(𝔭)`, while `ϑ` weights
only the primes themselves.  This file defines `ψ`, proves that the difference `ψ - ϑ` is exactly
the higher-prime-power sum estimated in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/HigherPrimePowers.lean`, and spends that estimate
on the transfer of an asymptotic `ψ(x) = δ x + o(x)` to `ϑ(x) = δ x + o(x)`.

Prime powers with `k ≥ 2` are kept visible throughout: `ψ` is *defined* with all of them present,
and their removal is a named hypothesis, `TauCeti.HasNegligibleHigherPrimePowers`, discharged for
the standard logarithmic weight by `TauCeti.standardPrimePowerRemoval`.  A different coefficient
system does not get that hypothesis for free; what it has to supply is the domination bound of
`TauCeti.primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight`.

## Main definitions

* `TauCeti.primePowerWeight` is the standard logarithmic prime-power weight, the value `log N(𝔭)`
  at `𝔭 ^ k` for every `k ≥ 1`.  It is the real form of the ideal von Mangoldt function of Layer 2
  on the prime powers.
* `TauCeti.primePsi` is its inclusive summatory function over the prime powers whose base lies in
  `S`: the number-field analogue of Chebyshev's `ψ`.
* `TauCeti.HasNegligibleHigherPrimePowers K S` says that `ψ - ϑ` is `o(x)`.
* `TauCeti.primeVonMangoldtWeight` is the same weight spread over *all* nonzero ideals, zero away
  from the prime powers with base in `S`, and `TauCeti.primeVonMangoldtCoeff` is its regrouping by
  absolute norm, an `ArithmeticFunction ℝ`.

## Main results

* `TauCeti.primePowerSummatory_indicator_sub_primeTheta` splits the exponent-one part off the
  standard weight restricted to any set of prime powers containing exactly the primes of `S`.
* `TauCeti.primePsi_sub_primeTheta` identifies `ψ - ϑ` with the higher-prime-power sum.
* `TauCeti.primePsi_le_ncard_mul_log`: for `x ≥ 1`, a finite set of primes contributes at most
  `#S · log x` to `ψ`, with `TauCeti.primePsi_isBigO_log_of_finite` and
  `TauCeti.primePsi_isLittleO_of_finite` its asymptotic forms.
* `TauCeti.standardPrimePowerRemoval` proves `HasNegligibleHigherPrimePowers K S` for every `S`,
  from the Layer 5 estimate `ψ(x) - ϑ(x) = O(√x log² x)`.
* `TauCeti.primeTheta_asymptotic_of_primePsi` and
  `TauCeti.primePsi_asymptotic_of_primeTheta` transfer a linear asymptotic across that difference,
  with `TauCeti.primeTheta_isEquivalent_of_primePsi` the equivalence form for a nonzero density.
* `TauCeti.primePsi_eq_sum_range` presents `ψ(x)` as the inclusive partial sum
  `∑_{n ≤ ⌊x⌋₊} a n` of the coefficient system, whose coefficients are nonnegative
  (`TauCeti.primeVonMangoldtCoeff_nonneg`) and supported on the prime powers
  (`TauCeti.primeVonMangoldtCoeff_eq_zero_of_not_isPrimePow`).
* `TauCeti.normCoeff_vonMangoldt` identifies the coefficient system of the full prime carrier with
  the Layer 1 regrouping of the Layer 2 ideal von Mangoldt function.
* `TauCeti.primeVonMangoldtCoeff_rat_natGenerator_pow` evaluates the coefficient system of any set
  of primes of `𝓞 ℚ` at a prime power, and `TauCeti.primeVonMangoldtCoeff_rat_le` bounds it by
  Mathlib's von Mangoldt function `Λ`.

## Roadmap role

This is Layer **10.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: "For the fixed
standard nonnegative logarithmic prime-power weight, use Layer 5 to prove
`standardPrimePowerRemoval : HasNegligibleHigherPrimePowers K S` and make
`primeTheta_asymptotic_of_primePsi` consume that named estimate."  It also supplies the arithmetic
half of Layer **10.1**, "Define `primePsi` with all prime powers present": the exact nonnegative
von Mangoldt coefficient system and the identity presenting `ψ` as its partial sum, which is the
shape in which a Tauberian theorem delivers its conclusion.  The analytic boundary package and
the resulting prime-number-theorem transfer are in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/Boundary.lean`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 7.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.

The rational-prime case of `ψ`, `ϑ` and their difference is Mathlib's
`Mathlib/NumberTheory/Chebyshev.lean`, whose `Chebyshev.theta_le_psi` and
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` are the analogues of
`TauCeti.primeTheta_le_primePsi` and `TauCeti.standardPrimePowerRemoval`; nothing is transported
from there, since the estimate consumed here is proved over prime ideals in Layer 5.
-/

 section

namespace TauCeti

open _root_.Filter _root_.NumberField
open scoped _root_.Asymptotics _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-! ### The standard logarithmic prime-power weight -/







/-- The standard logarithmic prime-power weight is positive. -/
theorem primePowerWeight_pos (A : IdealPrimePower K) : 0 < primePowerWeight A :=
  log_absNorm_asIdeal_pos (primePowerBase A)

/-- The standard logarithmic prime-power weight is nonnegative. -/
theorem primePowerWeight_nonneg (A : IdealPrimePower K) : 0 ≤ primePowerWeight A :=
  (primePowerWeight_pos A).le





/-! ### Chebyshev's `ψ` -/



variable {S : Set (HeightOneSpectrum (𝓞 K))} {x δ : ℝ}

/-- Chebyshev's `ψ` as an explicit sum over the inclusive prime-power carrier. -/
theorem primePsi_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primePsi K S x = ∑ A ∈ primePowersLE K x,
      {A : IdealPrimePower K | primePowerBase A ∈ S}.indicator primePowerWeight A := by
  rw [primePsi, primePowerSummatory_apply]



/-- Chebyshev's `ψ` is nonnegative. -/
theorem primePsi_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primePsi K S x :=
  primePowerSummatory_nonneg K _
    (fun A ↦ Set.indicator_nonneg (fun A _ ↦ primePowerWeight_nonneg A) A) x





/-! ### The higher prime powers as the gap between `ψ` and `ϑ` -/



/-- **The difference between `ψ` and `ϑ` is the higher-prime-power sum.**  Both sides run over the
prime powers whose base lies in `S`; the exponent-one part of `ψ` is exactly `ϑ`. -/
theorem primePsi_sub_primeTheta (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primePsi K S x - primeTheta K S x =
      primePowerSummatory K
        ({A : IdealPrimePower K | primePowerBase A ∈ S}.indicator higherPrimePowerWeight) x := by
  rw [primePsi]
  exact primePowerSummatory_indicator_sub_primeTheta _ S (fun v ↦ by simp) x



/-! ### Removing the higher prime powers -/



/-- The defining little-o estimate behind `TauCeti.HasNegligibleHigherPrimePowers`. -/
theorem hasNegligibleHigherPrimePowers_iff :
    HasNegligibleHigherPrimePowers K S ↔
      (fun x ↦ primePsi K S x - primeTheta K S x) =o[atTop] fun x : ℝ ↦ x :=
  Iff.rfl

/-- **Removal of the higher prime powers** for the standard logarithmic weight.  This is the
`o(x)` corollary of the Layer 5 bound `ψ(x) - ϑ(x) ≤ [K:ℚ] / (2 log 2) · √x log² x`. -/
theorem standardPrimePowerRemoval (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) : HasNegligibleHigherPrimePowers K S := by
  rw [hasNegligibleHigherPrimePowers_iff]
  simpa only [primePsi_sub_primeTheta] using primePowerSummatory_indicator_isLittleO K S



open Asymptotics in
/-- **A finite set of primes is `O(log x)` for `ψ`**, the asymptotic form of the bound above. -/
theorem primePsi_isBigO_log_of_finite (hS : S.Finite) :
    primePsi K S =O[atTop] Real.log := by
  refine IsBigO.of_bound S.ncard ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (primePsi_nonneg _ _),
    abs_of_nonneg (Real.log_nonneg hx)]
  exact primePsi_le_ncard_mul_log hS hx



/-- **Transfer of a linear asymptotic from `ψ` to `ϑ`.**  If the higher prime powers of `S` are
negligible and `ψ(x) = δ x + o(x)`, then `ϑ(x) = δ x + o(x)`. -/
theorem primeTheta_asymptotic_of_primePsi (h : HasNegligibleHigherPrimePowers K S)
    (hψ : (fun x ↦ primePsi K S x - δ * x) =o[atTop] fun x : ℝ ↦ x) :
    (fun x ↦ primeTheta K S x - δ * x) =o[atTop] fun x : ℝ ↦ x :=
  (hψ.sub h).congr' (Eventually.of_forall fun x ↦ by ring) EventuallyEq.rfl





/-! ### The von Mangoldt coefficient system of a set of primes -/

















































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
# The unramified primes carrying a prescribed Artin class

Let `L / K` be a finite Galois extension of number fields and let `C` be a conjugacy class in
`Gal(L/K)`. This file defines the set

`frobeniusPrimeSet K L C : Set (HeightOneSpectrum (𝓞 K))`

of height-one primes `𝔭` of `𝓞 K` that are unramified in `L` and whose Artin class is `C`. It is
the set whose density the Chebotarev density theorem computes.

## The dependent membership condition

`artinSymbol` is a *partial* construction: it takes an unramifiedness proof as an argument and has
no value at a ramified prime. So membership cannot be an equation between two total functions;
it is stated as

`∃ hur : (𝔭 is unramified in L), artinSymbol 𝔭.asIdeal hur = C`,

an existential over a proof. Membership is nonetheless unambiguous: it does not depend on which
unramifiedness proof witnesses it, and `mem_frobeniusPrimeSet_iff_artinSymbol_eq` turns the
existential into the plain equation `artinSymbol 𝔭.asIdeal hur = C` for whichever unramifiedness
proof `hur` the caller has in hand.

The alternative — a total `Gal(L/K)`-valued or `ConjClasses`-valued function taking a junk value
at the ramified primes — is worse for this set: the junk value carries no arithmetic content, yet
the ramified primes would sit inside the fibre of whichever class it names, so the fibres would
neither cover the unramified primes exactly nor be pinned down by a Frobenius element there. The
existential is what keeps the fibres free of them.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimeSet`: the primes of `𝓞 K` unramified in `L` whose Artin
  class is `C`.

## Main results

* `NumberField.Chebotarev.mem_frobeniusPrimeSet_iff_artinSymbol_eq`: proof-independence — with
  any unramifiedness proof in hand, membership is the equation `artinSymbol 𝔭.asIdeal hur = C`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_iff_exists_isArithFrobAt`: for an unramified
  `𝔭` and an element `σ`, membership in the fibre of `[σ]` says exactly that `σ` is an arithmetic
  Frobenius at *some* prime of `𝓞 L` above `𝔭`.
* `NumberField.Chebotarev.frobeniusPrimeSet_map_autCongr`: equivariance — an isomorphism
  `e : L ≃ₐ[K] L'` of extensions of `K` matches the fibre of `C` in `L` with the fibre in `L'` of
  the image of `C` under the induced isomorphism `AlgEquiv.autCongr e` of Galois groups.
* `NumberField.Chebotarev.frobeniusPrimeSet_subset_map_restrictNormalHom`: a fibre over `L` lies
  in the fibre over a Galois subextension `M` of the restricted class.
* `NumberField.Chebotarev.disjoint_frobeniusPrimeSet`: distinct classes have disjoint fibres.
* `NumberField.Chebotarev.iUnion_frobeniusPrimeSet`: the fibres cover exactly the complement of
  `ramifiedPrimes K L`, so `existsUnique_mem_frobeniusPrimeSet` partitions the unramified primes
  and `finite_compl_iUnion_frobeniusPrimeSet` records that the discarded remainder is finite.

The last two are what let the density arguments discard a finite exceptional set and then work
one class at a time: a lower density bound for each class can be squeezed against a partition of
a cofinite set, which is how the crossing argument produces exact densities.
-/

 section

open _root_.Ideal
open scoped _root_.NumberField

open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]



/-- Membership in `frobeniusPrimeSet`, unfolded. Downstream files should open the definition
through this lemma rather than through defeq. -/
@[simp]
theorem mem_frobeniusPrimeSet_iff {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    𝔭 ∈ frobeniusPrimeSet K L C ↔
      ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q, artinSymbol 𝔭.asIdeal hur = C :=
  Iff.rfl

















section IsoOfExtensions

variable {L' : Type*} [Field L'] [NumberField L'] [Algebra K L'] [IsGalois K L']



end IsoOfExtensions

section RestrictNormal

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
  [IsGalois K M]



end RestrictNormal











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
# Frobenius von Mangoldt coefficients

For a conjugacy class `C` in the Galois group of a finite Galois extension `L / K`, this file
defines the von Mangoldt coefficient and summatory functions restricted to `C`. A prime power
`𝔭 ^ j` belongs to the `C`-fibre when the `j`-th power of the Artin class of `𝔭` is `C`.
Consequently a prime whose Artin class is not `C` can still contribute through a higher power.

The definitions retain only unramified primes: the Artin symbol is never evaluated at a ramified
prime. The exponent-one terms form `frobeniusTheta`; all higher prime powers are dominated by the
unrestricted higher-prime-power weight from the arithmetic Dirichlet-series development, hence
their contribution is `o(x)`.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimePowerSet`: prime powers selected by the powered Artin
  class.
* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff`: the corresponding nonnegative arithmetic
  function, regrouped by absolute norm.
* `NumberField.Chebotarev.frobeniusPsi` and `NumberField.Chebotarev.frobeniusTheta`: the weighted
  prime-power and prime summatory functions.
* `NumberField.Chebotarev.frobeniusPrimeCount`: the number of primes of norm at most `x`
  whose arithmetic Frobenius class is `C`, with `NumberField.Chebotarev.natCast_frobeniusPrimeCount`
  identifying it with the generic count of `frobeniusPrimeSet`.

## Main results

* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff_rat_natGenerator_pow`: over `ℚ`, the
  coefficient at `p ^ (k + 1)` is the powered Frobenius weight of `𝔭 ^ (k + 1)`, the only ideal
  of that norm.
* `NumberField.Chebotarev.frobeniusPsi_eq_sum_range`: `frobeniusPsi` is the inclusive partial sum
  of `frobeniusVonMangoldtCoeff`.
* `NumberField.Chebotarev.frobeniusPsi_eq_sum_Icc`: the same sum indexed from `1`.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory`: their
  difference is exactly the contribution from exponents at least two.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_le`: that difference is bounded by
  the unrestricted higher-prime-power tail.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_isLittleO`: this difference is `o(x)`.

The coefficient convention follows Neukirch, *Algebraic Number Theory*, Chapter VII. The
construction reuses Tau Ceti's generic prime-power counting and removal estimates.
-/

 section

namespace NumberField.Chebotarev

open _root_.Filter _root_.TauCeti
open scoped _root_.Asymptotics _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- The powered-class convention follows `TauCetiRoadmap/Chebotarev/Suggested.lean`.


/-- Membership in `frobeniusPrimePowerSet`, unfolded. -/
@[simp]
theorem mem_frobeniusPrimePowerSet_iff {A : IdealPrimePower K}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    A ∈ frobeniusPrimePowerSet K L C ↔
      ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
          Algebra.IsUnramifiedAt (𝓞 K) Q,
        artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C :=
  Iff.rfl



-- Not `@[simp]`: `mem_frobeniusPrimePowerSet_iff` together with `primePowerBase_ofPrime`,
-- `primePowerExponent_ofPrime` and `ConjClasses.pow_one` already rewrites the left-hand side.
/-- At exponent one, the powered Frobenius fibre is the ordinary Frobenius prime set. -/
theorem ofPrime_mem_frobeniusPrimePowerSet_iff {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    IdealPrimePower.ofPrime 𝔭 ∈ frobeniusPrimePowerSet K L C ↔
      𝔭 ∈ frobeniusPrimeSet K L C := by
  simp only [mem_frobeniusPrimePowerSet_iff, primePowerBase_ofPrime,
    primePowerExponent_ofPrime, ConjClasses.pow_one, mem_frobeniusPrimeSet_iff]























/-- `frobeniusPsi` as an explicit sum over the inclusive prime-power carrier. -/
theorem frobeniusPsi_apply (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    frobeniusPsi K L C x =
      ∑ A ∈ primePowersLE K x, frobeniusPrimePowerWeight K L C A := by
  rw [frobeniusPsi, primePowerSummatory_apply]



/-- The Frobenius `ϑ` function is the generic logarithmically weighted prime count of its
Frobenius prime set. -/
theorem frobeniusTheta_def (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    frobeniusTheta K L C x = primeTheta K (frobeniusPrimeSet K L C) x := by
  rw [frobeniusTheta]

/-- The Frobenius prime count is the generic count of its prime set. -/
theorem natCast_frobeniusPrimeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    (frobeniusPrimeCount K L C x : ℝ) = primeCount K (frobeniusPrimeSet K L C) x := by
  classical
  simpa only [frobeniusPrimeCount] using
    (primeCount_eq_card (frobeniusPrimeSet K L C) x).symm























-- The powered filter is exercised here: this is the term a definition filtering on
-- `artinSymbol 𝔭 = C` alone would lose. The order-four configuration is not vacuous —
-- `ConjClasses.mk_ne_mk_of_orderOf_ne` separates the two classes for *every* element of order
-- four, its square having order two, and the cyclic group of order four realises such an element
-- concretely.












/-- The gap between the Frobenius `ψ` and `ϑ` functions is exactly the sum of the higher
prime-power weight over the `C`-fibre. -/
theorem frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory (C : ConjClasses (L ≃ₐ[K] L))
    (x : ℝ) :
    frobeniusPsi K L C x - frobeniusTheta K L C x =
      primePowerSummatory K
        ((frobeniusPrimePowerSet K L C).indicator higherPrimePowerWeight) x := by
  -- `frobeniusPrimePowerWeight K L C` unfolds to `(frobeniusPrimePowerSet K L C).indicator
  -- primePowerWeight`, the restricted standard weight the generic splitting lemma expects.
  rw [frobeniusPsi, frobeniusTheta]
  exact primePowerSummatory_indicator_sub_primeTheta _ _
    (fun 𝔭 ↦ ofPrime_mem_frobeniusPrimePowerSet_iff) x





/-- The higher-prime-power contribution to Frobenius `ψ` is `o(x)`. -/
theorem frobeniusPsi_sub_frobeniusTheta_isLittleO (C : ConjClasses (L ≃ₐ[K] L)) :
    (fun x ↦ frobeniusPsi K L C x - frobeniusTheta K L C x) =o[atTop]
      fun x : ℝ ↦ x := by
  simpa only [frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory] using
    primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight K zero_le_one fun A ↦ by
      rw [Real.norm_of_nonneg (Set.indicator_nonneg
        (fun A _ ↦ higherPrimePowerWeight_nonneg A) A), one_mul]
      exact Set.indicator_apply_le' (fun _ ↦ le_rfl) fun _ ↦ higherPrimePowerWeight_nonneg A

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
# The Frobenius `ψ` fibres partition Chebyshev's `ψ`

Let `L / K` be a finite Galois extension of number fields with group `G`. A prime power `𝔭 ^ j`
with `𝔭` unramified in `L` lies in the powered Frobenius fibre of exactly one conjugacy class of
`G`, namely `(artinSymbol 𝔭) ^ j`, and a prime power based at a ramified prime lies in none. So the
Frobenius `ψ` functions of all conjugacy classes add up to Chebyshev's `ψ` of `K` with the ramified
primes removed:

```text
∑_C ψ_C(x) + ψ_{ramifiedPrimes K L}(x) = ψ_K(x),
```

and the correction is `O(log x)` because the ramified set is finite.

These identities supply the partition input for the weighted crossing. The later squeeze also
requires the cyclotomic weighted theorem and its consequence `ψ_K(x) / x → 1`.

## Main results

* `NumberField.Chebotarev.sum_frobeniusPrimePowerWeight`: at a single prime power, the Frobenius
  weights of all classes add up to the von Mangoldt weight if the base is unramified, and to `0`
  otherwise.
* `NumberField.Chebotarev.sum_frobeniusPsi_add_primePsi_ramifiedPrimes`: the Frobenius `ψ`
  functions and `ψ` of the ramified primes add up to `ψ_K`.
* `NumberField.Chebotarev.primePsi_univ_sub_sum_frobeniusPsi_isBigO_log`: the Frobenius `ψ`
  functions account for `ψ_K` up to `O(log x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
-/

 section

namespace NumberField.Chebotarev

open _root_.Filter _root_.TauCeti
open scoped _root_.Asymptotics _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]



open scoped Classical in
variable (K L) in
/-- **The Frobenius `ψ` fibres partition Chebyshev's `ψ`.** Summed over all conjugacy classes of
`Gal(L/K)`, the Frobenius `ψ` functions count every prime power based at a prime unramified in `L`
exactly once; adding `ψ` of the finite set `ramifiedPrimes K L` gives `ψ_K`. -/
theorem sum_frobeniusPsi_add_primePsi_ramifiedPrimes (x : ℝ) :
    ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPsi K L C x +
        primePsi K (ramifiedPrimes K L : Set (HeightOneSpectrum (𝓞 K))) x =
      primePsi K Set.univ x := by
  simp only [frobeniusPsi_apply, primePsi_apply]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [sum_frobeniusPrimePowerWeight]
  by_cases hA : primePowerBase A ∈ ramifiedPrimes K L <;>
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.mem_coe, Set.mem_univ, hA,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false, zero_add, add_zero]

open scoped Classical in
variable (K L) in
/-- **The Frobenius `ψ` fibres account for `ψ_K` up to `O(log x)`.** The only prime powers missed by
all Frobenius fibres are those based at the finitely many primes of `ramifiedPrimes K L`. -/
theorem primePsi_univ_sub_sum_frobeniusPsi_isBigO_log :
    (fun x : ℝ ↦ primePsi K Set.univ x - ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPsi K L C x)
      =O[atTop] Real.log := by
  refine (primePsi_isBigO_log_of_finite (ramifiedPrimes K L).finite_toSet).congr_left fun x ↦ ?_
  rw [← sum_frobeniusPsi_add_primePsi_ramifiedPrimes K L x, add_sub_cancel_left]

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
# Weighted Chebotarev for cyclotomic extensions

Let `F = K(μ_m)` be a cyclotomic extension of a number field `K`, with group `G = Gal(F/K)`. This
file proves the prime-number-theorem form of Chebotarev's theorem for `F / K`: for every `σ ∈ G`,

```text
ψ_σ(x) = x / #G + o(x),
```

where `ψ_σ = frobeniusPsi K F (ConjClasses.mk σ)` counts the prime powers `𝔭 ^ j` of `K` with
`𝔭` unramified in `F` and `Frob(𝔭) ^ j = σ`, weighted by `log N𝔭`. Taking `F = K` gives the
prime ideal theorem `ψ_K(x) = x + o(x)` for every number field `K`.

The proof applies the Wiener--Ikehara theorem `TauCeti.LSeries.wienerIkehara` to the nonnegative
coefficients of `ψ_σ`. By the character expansion
`NumberField.Chebotarev.LSeries_frobeniusVonMangoldtCoeff_eq_sum_logDeriv`, their Dirichlet series
is `(1 / #G) ∑_χ χ(σ)⁻¹ (-L_χ'(s) / L_χ(s))` on `Re s > 1`, where `L_χ` is the `L`-series of the
Galois character weight of `χ`. The required boundary behaviour on `Re s ≥ 1` comes term by term:

* for `χ ≠ 1`, the continued series `cyclotomicCharacterSeriesC K F χ` is holomorphic across
  `Re s = 1` and nonzero on `Re s ≥ 1`, so `-L_χ'/L_χ` extends continuously to `Re s ≥ 1`;
* for `χ = 1`, `L_1` is the Dedekind zeta function of `K` with the Euler factors at the ramified
  primes deleted. The function `H(s) = (s - 1) L_1(s)` continues holomorphically across
  `Re s = 1`, takes the value `ρ = Res_{s=1} ζ_K · ∏_{𝔭 ramified} (1 - N𝔭⁻¹) ≠ 0` at `s = 1`, and
  does not vanish elsewhere on `Re s ≥ 1`. Hence `-L_1'/L_1 - 1/(s - 1) = -H'/H` extends
  continuously to `Re s ≥ 1`.

So the Frobenius von Mangoldt series of `σ` minus `(1 / #G) / (s - 1)` extends continuously to
`Re s ≥ 1`, which is exactly the Wiener--Ikehara hypothesis with residue `1 / #G`.

## Main results

* `NumberField.Chebotarev.frobeniusPsi_asymptotic_of_isCyclotomicExtension`: for `F = K(μ_m)`,
  `ψ_σ(x) = x / #Gal(F/K) + o(x)`.
* `NumberField.Chebotarev.primePsi_univ_asymptotic`: the prime ideal theorem
  `ψ_K(x) = x + o(x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
* The regularization `(s - 1) L(s)`, holomorphic near `Re s ≥ 1`, follows
  Mathlib's `DirichletCharacter.LFunctionTrivChar₁` and
  `DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁`
  (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`), used there for Dirichlet's theorem
  on primes in arithmetic progressions.
* The character-sum boundary function follows Mathlib's
  `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux` and its continuity and agreement
  theorems in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`.
-/

 section

open _root_.Asymptotics _root_.Complex _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.Topology

namespace NumberField.Chebotarev

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]



open scoped Classical in
variable (K) in
/-- **The prime ideal theorem, for Chebyshev's `ψ`.** For every number field `K`, the von Mangoldt
summatory function `ψ_K(x) = ∑_{N𝔭^j ≤ x} log N𝔭` of `K` satisfies `ψ_K(x) = x + o(x)`. -/
theorem primePsi_univ_asymptotic :
    (fun x : ℝ ↦ primePsi K Set.univ x - x) =o[atTop] fun x : ℝ ↦ x := by
  have : IsCyclotomicExtension {1} K K :=
    IsCyclotomicExtension.singleton_one_of_algebraMap_bijective fun x ↦ ⟨x, rfl⟩
  have hψ := frobeniusPsi_asymptotic_of_isCyclotomicExtension K K 1 1
  have hsum := (primePsi_univ_sub_sum_frobeniusPsi_isBigO_log K K).trans_isLittleO
    Real.isLittleO_log_id_atTop
  -- `Gal(K/K)` is trivial, so it has a single conjugacy class.
  have : Subsingleton (ConjClasses (K ≃ₐ[K] K)) := Quot.Subsingleton
  refine (hsum.add hψ).congr (fun x ↦ ?_) fun _ ↦ rfl
  rw [Fintype.sum_subsingleton _ (ConjClasses.mk 1), Nat.card_unique]
  ring

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
# Contracting Frobenius `ϑ` and `ψ` from a cyclic fixed field

Let `L / K` be a finite Galois extension of number fields, let `C` be a conjugacy class of
`Gal(L/K)`, choose `sigma ∈ C`, and put `E = L ^ <sigma>`.  This file proves the exact identity

```text
∑_{𝔓 ∈ S_E, N 𝔓 ≤ x} log N 𝔓 = (#G / (#C * orderOf sigma)) * ϑ_C(x),
```

where `S_E` is the set of primes `𝔓` of `E` whose relative Artin class in `L / E` is represented by
`sigma`, that do not lie above `ramifiedPrimes K L`, and that have residue degree one over `K`.

There is no error term.  Away from the ramified primes, a prime `𝔓` of the relative fibre has
residue degree one over `K` exactly when the prime `𝔭` of `K` below it lies in the Frobenius fibre
of `C` (`NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet`); then
`N 𝔓 = N 𝔭`, and over each such `𝔭` there are exactly `#G / (#C * orderOf sigma)` of them
(`NumberField.Chebotarev.fixedField_frobenius_fiber_card`).

The identity concerns `ϑ` at residue degree one only.  The other primes of the relative fibre have
residue degree at least two over `ℚ` or lie above `ramifiedPrimes K L`, so they are majorized by
the unrestricted sums appearing in `NumberField.Chebotarev.frobeniusDiscard_isLittleO` over
`L ^ <sigma>`.  In general there is no such identity for `ψ`: a prime power `𝔓 ^ m` with `m ≥ 2`
is selected by the `m`-th power of its Frobenius, and the prime of `K` below it need not have
class `C`.  So the transfer of `ψ` is only asymptotic,

```text
ψ_sigma^{L/E}(x) = (#G / (#C * orderOf sigma)) * ψ_C^{L/K}(x) + o(x),
```

obtained by removing the prime powers with `m ≥ 2` on both sides, applying the exact identity to
what remains, and discarding the relative primes of higher residue degree or above
`ramifiedPrimes K L`.

## Main results

* `NumberField.Chebotarev.primeTheta_fixedField_eq_mul_frobeniusTheta`: the residue-degree-one
  part of the relative Frobenius `ϑ` over `L ^ <sigma>`, away from the primes above
  `ramifiedPrimes K L`, is the fixed-field multiplicity times `frobeniusTheta K L C`.
* `NumberField.Chebotarev.frobeniusPsi_fixedField_sub_mul_frobeniusPsi_isLittleO`: the relative
  Frobenius `ψ` of `sigma` over `L ^ <sigma>` is the fixed-field multiplicity times
  `frobeniusPsi K L C`, up to `o(x)`.
* `NumberField.Chebotarev.frobeniusPsi_fixedField_asymptotic_iff`: hence the relative Frobenius
  `ψ` of `sigma` is `δ x + o(x)` exactly when `frobeniusPsi K L C` is `δ x + o(x)` divided by
  the fixed-field multiplicity.
* `NumberField.Chebotarev.frobeniusPsi_asymptotic_of_fixedField`: its specialisation at the cyclic
  value `δ = 1 / orderOf sigma`, which lands the Chebotarev value `#C / #G` over `K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter I, §5.
-/

 section

open _root_.Filter _root_.IntermediateField
open scoped _root_.Asymptotics _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

open _root_.TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]











/-- **Chebotarev's weighted value, from the cyclic fibre.** If the relative Frobenius `ψ` of
`sigma` over `E = L ^ <sigma>` is `x / orderOf sigma + o(x)`, the value for a fibre of the cyclic
extension `L / E` of degree `orderOf sigma`, then `frobeniusPsi K L C x = (#C / #G) x + o(x)`.

This is the weighted counterpart of `hasDirichletDensity_frobeniusPrimeSet_of_fixedField`: it
reduces the prime-number-theorem form of Chebotarev for an arbitrary class to the cyclic
extension `L / E`. -/
theorem frobeniusPsi_asymptotic_of_fixedField (C : ConjClasses (L ≃ₐ[K] L))
    (sigma : L ≃ₐ[K] L) (hsigma : sigma ∈ C.carrier)
    (h : (fun x : ℝ ↦ frobeniusPsi ↥(fixedField (Subgroup.zpowers sigma)) L
        (ConjClasses.mk sigma.toFixedFieldAlgEquiv) x - 1 / orderOf sigma * x)
          =o[atTop] (fun x : ℝ ↦ x)) :
    (fun x : ℝ ↦ frobeniusPsi K L C x -
      (Nat.card C.carrier / Nat.card (L ≃ₐ[K] L) : ℝ) * x) =o[atTop] (fun x : ℝ ↦ x) := by
  exact C.one_div_orderOf_div_card_div_card_carrier_mul_orderOf (K := ℝ) sigma hsigma ▸
    (frobeniusPsi_fixedField_asymptotic_iff C sigma hsigma).mp h

end NumberField.Chebotarev

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
namespace TauCeti.NumberField
end TauCeti.NumberField
namespace TauCeti.NumberField.Chebotarev
end TauCeti.NumberField.Chebotarev
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Chebotarev density theorem, for Chebyshev's `ψ`

Let `L / K` be a finite Galois extension of number fields with group `G`, and let `C` be a
conjugacy class of `G`. This file proves the prime-number-theorem form of Chebotarev's theorem,

```text
ψ_C(x) = (#C / #G) x + o(x),
```

where `ψ_C = frobeniusPsi K L C` sums `log N𝔭` over the prime powers `𝔭 ^ j` of `K` with `𝔭`
unramified in `L` and `Frob(𝔭) ^ j ∈ C`.

The proof is the weighted form of the cyclotomic crossing behind
`NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet`; in particular, the tagged-class
crossing follows the proof of `NumberField.Chebotarev.hasDirichletDensity_abelianFrobenius`.

* For abelian `G` and `σ ∈ G` of order `f`, pick an auxiliary prime `q` with `f ^ r ∣ q - 1`
  and cross with `M = L(μ_q)`, so that `Gal(M/K) ≃ G × (ZMod q)ˣ`. For each tag `τ` with
  `f ∣ orderOf τ`, the field `E_τ` fixed by `(σ, τ)` has `M` as a `q`-th cyclotomic extension,
  so the cyclotomic weighted theorem over `E_τ` and the contraction across the cyclic fixed field
  give `ψ_{(σ, τ)}(x) = x / #Gal(M/K) + o(x)` over `K`. The tagged classes are distinct classes
  over the class of `σ`, so their `ψ` functions add up to at most `ψ_σ`: for a fixed `q`, the
  limit in `x` gives `liminf ψ_σ(x) / x ≥ (1 - 2 ^ (-r)) ^ #f.primeFactors / #G`, and only then
  does `r` grow, giving `liminf ψ_σ(x) / x ≥ 1 / #G`.
* The `ψ` functions of all classes add up to `ψ_K(x) = x + o(x)` up to `O(log x)`, so these
  lower bounds saturate the total and each of them is the limit.
* For a general class `C ∋ σ`, the extension `L / L ^ ⟨σ⟩` is cyclic, and the contraction across
  the cyclic fixed field carries the abelian result down to `C`.

## Main results

* `NumberField.Chebotarev.frobeniusPsi_asymptotic_of_mul_comm`: for abelian `G` and `σ ∈ G`,
  `ψ_σ(x) = x / #G + o(x)`.
* `NumberField.Chebotarev.frobeniusPsi_asymptotic`: for every conjugacy class `C` of `G`,
  `ψ_C(x) = (#C / #G) x + o(x)`.
* `NumberField.Chebotarev.tendsto_frobeniusPsi`: the same, as `ψ_C(x) / x → #C / #G`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
* H. W. Lenstra Jr. and P. Stevenhagen, "Chebotarëv and his density theorem",
  *Math. Intelligencer* 18 (1996), 26–37, for the cyclotomic crossing.
-/

open _root_.Asymptotics _root_.Filter _root_.NumberField _root_.TauCeti _root_.TauCeti.NumberField.Chebotarev
open scoped _root_.NumberField _root_.TauCeti.NumberField _root_.Topology

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- **One auxiliary prime.** In an abelian extension, the Frobenius `ψ` of `σ` eventually exceeds
-- `δ x` for every `δ` below `(1 - 2 ^ (-r)) ^ #(orderOf σ).primeFactors / #G`, for every `r ≥ 1`.


-- Letting the level of the auxiliary prime grow: in an abelian extension, the Frobenius `ψ` of
-- `σ` eventually exceeds `δ x` for every `δ < 1 / #G`.


 section



variable (K L) in
/-- **The Chebotarev density theorem, for Chebyshev's `ψ`.** For a finite Galois extension `L / K`
of number fields and a conjugacy class `C` of `Gal(L/K)`, the Frobenius `ψ` function of `C`
satisfies `ψ_C(x) = (#C / #Gal(L/K)) x + o(x)`. -/
theorem frobeniusPsi_asymptotic (C : ConjClasses (L ≃ₐ[K] L)) :
    (fun x : ℝ ↦ frobeniusPsi K L C x -
      (Nat.card C.carrier / Nat.card (L ≃ₐ[K] L) : ℝ) * x) =o[atTop] fun x : ℝ ↦ x := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  refine frobeniusPsi_asymptotic_of_fixedField _ σ ConjClasses.mem_carrier_mk ?_
  -- `Gal(L / L ^ ⟨σ⟩)` is generated by `σ`, so it is cyclic and hence abelian.
  have : IsCyclic (L ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨_, AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top σ⟩
  exact AlgEquiv.card_algEquiv_fixedField_zpowers σ ▸ frobeniusPsi_asymptotic_of_mul_comm
    IsCyclic.commGroup.mul_comm σ.toFixedFieldAlgEquiv



end

end NumberField.Chebotarev

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
# The prime ideal theorem

`NumberField.Set.HasNaturalDensity` measures a set `S` of primes of a number field `K` by the
ratio `π_S(x) / π_K(x)` of prime counts. This file derives the size of the denominator `π_K(x)`,
the prime ideal theorem, in its `ϑ` and `π` forms from the `ψ` form
`NumberField.Chebotarev.primePsi_univ_asymptotic`, which is proved by the Wiener--Ikehara theorem
with no boundary hypothesis:

```text
ϑ_K(x) = x + o(x),      π_K(x) = Li(x) + o(x / log x),      π_K(x) ~ Li(x).
```

The two passages are the generic transfers `TauCeti.primeTheta_asymptotic_of_primePsi`, which
removes the prime powers with exponent at least two, and
`TauCeti.primeCount_sub_mul_logIntegral_isLittleO`, which is Abel summation.

## Main results

* `NumberField.Chebotarev.primeTheta_univ_asymptotic`: `ϑ_K(x) = x + o(x)`.
* `NumberField.Chebotarev.primeCount_univ_sub_logIntegral_isLittleO`:
  `π_K(x) = Li(x) + o(x / log x)`.
* `NumberField.Chebotarev.primeCount_univ_isEquivalent_logIntegral`: `π_K(x) ~ Li(x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13, for natural density and the
  Chebotarev density theorem.
* S. Lang, *Algebraic Number Theory*, Chapter XV, for the prime ideal theorem and the passage
  from `ψ` to `π`.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.Topology

namespace NumberField.Chebotarev

variable (K : Type*) [Field K] [NumberField K]

/-- **The prime ideal theorem, for `ϑ`.** For every number field `K`, the logarithmically weighted
prime count `ϑ_K(x) = ∑_{N𝔭 ≤ x} log N𝔭` satisfies `ϑ_K(x) = x + o(x)`. -/
theorem primeTheta_univ_asymptotic :
    (fun x : ℝ ↦ primeTheta K Set.univ x - x) =o[atTop] fun x : ℝ ↦ x := by
  simpa using primeTheta_asymptotic_of_primePsi (δ := 1) (standardPrimePowerRemoval K Set.univ)
    (by simpa using primePsi_univ_asymptotic K)

/-- **The prime ideal theorem, with the logarithmic integral.** For every number field `K`, the
number of primes of `K` of norm at most `x` is `Li(x) + o(x / log x)`. -/
theorem primeCount_univ_sub_logIntegral_isLittleO :
    (fun x : ℝ ↦ primeCount K Set.univ x - Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x := by
  simpa using primeCount_sub_mul_logIntegral_isLittleO (δ := 1)
    ((primeTheta_univ_asymptotic K).congr_left fun x ↦ by rw [one_mul])



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
# Prime counting and natural density for Frobenius classes

For a finite Galois extension `L/K` of number fields, the primes of `K` in a conjugacy class
`C`, counted by `NumberField.Chebotarev.frobeniusPrimeCount`, have count asymptotic to
`(#C / #Gal(L/K)) Li(x)`. The weighted Chebotarev theorem gives the corresponding result for
`ψ_C`; removing higher prime powers and Abel summation give the count.
Comparison with the prime ideal theorem for all primes then gives natural density.

## Main results

* `NumberField.Chebotarev.tendsto_frobeniusTheta`: the weighted prime count divided by `x`
  tends to `#C / #Gal(L/K)`.
* `NumberField.Chebotarev.tendsto_frobeniusPrimeCount`: the prime count divided by `x / log x`
  tends to `#C / #Gal(L/K)`.
* `NumberField.Chebotarev.frobeniusPrimeCount_isEquivalent_logIntegral`: the prime count is
  asymptotic to `(#C / #Gal(L/K)) Li(x)`.
* `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`: the same ratio is the natural
  density of the Frobenius prime set.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV, for the passage from `ψ` to prime counting.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.NumberField _root_.TauCeti
open scoped _root_.NumberField _root_.Topology

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- The logarithmically weighted count of a Frobenius class satisfies
`ϑ_C(x) = (#C / #Gal(L/K)) x + o(x)`. -/
private theorem NumberField.Chebotarev.frobeniusTheta_asymptotic (C : _root_.ConjClasses (L ≃ₐ[K] L)) :
    (fun x : ℝ ↦ _root_.NumberField.Chebotarev.frobeniusTheta K L C x -
      ((_root_.Nat.card C.carrier : ℝ) / _root_.Nat.card (L ≃ₐ[K] L)) * x) =o[_root_.Filter.atTop] _root_.id := by
  have h := (_root_.NumberField.Chebotarev.frobeniusPsi_asymptotic K L C).sub
    (_root_.NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_isLittleO C)
  exact h.congr_left fun x ↦ by ring



/-- The Frobenius prime count is `(#C / #Gal(L/K)) Li(x) + o(x / log x)`. -/
private theorem NumberField.Chebotarev.frobeniusPrimeCount_sub_mul_logIntegral_isLittleO
    (C : _root_.ConjClasses (L ≃ₐ[K] L)) :
    (fun x : ℝ ↦ (_root_.NumberField.Chebotarev.frobeniusPrimeCount K L C x : ℝ) -
      ((_root_.Nat.card C.carrier : ℝ) / _root_.Nat.card (L ≃ₐ[K] L)) * _root_.TauCeti.Real.logIntegral x)
      =o[_root_.Filter.atTop] fun x : ℝ ↦ x / _root_.Real.log x := by
  simpa only [_root_.NumberField.Chebotarev.natCast_frobeniusPrimeCount] using
    (_root_.TauCeti.primeCount_sub_mul_logIntegral_isLittleO (K := K)
      (S := _root_.NumberField.Chebotarev.frobeniusPrimeSet K L C)
      (δ := (_root_.Nat.card C.carrier : ℝ) / _root_.Nat.card (L ≃ₐ[K] L))
      (by simpa only [← _root_.NumberField.Chebotarev.frobeniusTheta_def] using _root_.NumberField.Chebotarev.frobeniusTheta_asymptotic K L C))





/-- Natural-density Chebotarev: among the primes of `K`, the primes with arithmetic Frobenius
class `C` have density `#C / #Gal(L/K)`. -/
theorem solution (C : _root_.ConjClasses (L ≃ₐ[K] L)) :
    _root_.NumberField.Set.HasNaturalDensity (_root_.NumberField.Chebotarev.frobeniusPrimeSet K L C)
      ((_root_.Nat.card C.carrier : ℝ) / _root_.Nat.card (L ≃ₐ[K] L)) := by
  apply _root_.NumberField.Set.hasNaturalDensity_of_isLittleO_logIntegral
  · simpa only [_root_.NumberField.Chebotarev.natCast_frobeniusPrimeCount] using
      _root_.NumberField.Chebotarev.frobeniusPrimeCount_sub_mul_logIntegral_isLittleO K L C
  · exact _root_.NumberField.Chebotarev.primeCount_univ_sub_logIntegral_isLittleO K

end NumberField.Chebotarev

end
end
