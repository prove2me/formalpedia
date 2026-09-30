-- Prove2me | solution 1 for NumberField.Chebotarev.frobeniusPsi_fixedField_sub_mul_frobeniusPsi_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:03:04.472412+00:00
-- url     : https://prove2.me/submissions/e1afcf5f-4aa3-4552-9a19-aef869b13b9b

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_FieldTheory_Galois_FixedField
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_HigherPrimePowers
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimesAboveRamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_ResidueDegree
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_PrimesAbove
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
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
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_NumberField_Chebotarev_fixedField_frobenius_fiber_card
import Theorems.Thm_NumberField_Chebotarev_inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet
import Theorems.Thm_TauCeti_primeCount_higherDegreePrimes_le
import Theorems.Thm_TauCeti_primePowerSummatory_indicator_sub_primeTheta
import Theorems.Thm_TauCeti_primePowerSummatory_isBigO_of_le_higherPrimePowerWeight
import Theorems.Thm_TauCeti_primePsi_le_ncard_mul_log

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

















/-! ### Generic summatory functions -/



/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]



/-- Summation distributes over pointwise addition of weights. -/
theorem summatory_add {M : Type*} [AddCommMonoid M] (w₁ w₂ : ι → M) (x : ℝ) :
    summatory N (w₁ + w₂) x = summatory N w₁ x + summatory N w₂ x := by
  simp [summatory, Finset.sum_add_distrib]











/-- The summatory function of a pointwise nonnegative real weight is nonnegative. -/
theorem summatory_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (x : ℝ) : 0 ≤ summatory N w x :=
  Finset.sum_nonneg fun i _ ↦ hw i

/-- Pointwise comparison of real weights gives the same comparison of their summatory functions. -/
theorem summatory_le_summatory {w₁ w₂ : ι → ℝ} (h : ∀ i, w₁ i ≤ w₂ i) (x : ℝ) :
    summatory N w₁ x ≤ summatory N w₂ x :=
  Finset.sum_le_sum fun i _ ↦ h i











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

/-- The logarithmically weighted prime count as an explicit sum over the inclusive carrier. -/
theorem primeTheta_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x =
      ∑ v ∈ primesLE K x, S.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v :=
  by rw [primeTheta, primeSummatory_apply]

/-- The unweighted prime count as an explicit sum over the inclusive carrier. -/
theorem primeCount_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = ∑ v ∈ primesLE K x, S.indicator 1 v := by
  rw [primeCount, primeSummatory_apply]









/-- The absolute norm of a height-one prime is positive, as a real number. -/
theorem absNorm_asIdeal_real_pos (v : HeightOneSpectrum (𝓞 K)) :
    0 < (Ideal.absNorm v.asIdeal : ℝ) :=
  lt_of_lt_of_le zero_lt_two (two_le_absNorm_asIdeal_real v)

/-- The logarithm of the absolute norm of a height-one prime is positive. -/
theorem log_absNorm_asIdeal_pos (v : HeightOneSpectrum (𝓞 K)) :
    0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
  Real.log_pos (by linarith [two_le_absNorm_asIdeal_real v])

/-- The logarithm of the absolute norm of a height-one prime is nonnegative. -/
theorem log_absNorm_asIdeal_nonneg (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
  (log_absNorm_asIdeal_pos v).le



/-- The logarithmically weighted prime count is nonnegative. -/
theorem primeTheta_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primeTheta K S x :=
  summatory_nonneg _ (fun v ↦ Set.indicator_nonneg
    (fun v _ ↦ log_absNorm_asIdeal_nonneg v) v) x

/-- The unweighted prime count is nonnegative. -/
theorem primeCount_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primeCount K S x :=
  summatory_nonneg _ (fun v ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) v) x





/-- Enlarging the prime set can only increase the logarithmically weighted count. -/
theorem primeTheta_mono_set (hST : S ⊆ T) (x : ℝ) : primeTheta K S x ≤ primeTheta K T x :=
  summatory_le_summatory _ (fun v ↦ Set.indicator_le_indicator_of_subset hST
    log_absNorm_asIdeal_nonneg v) x











/-- The weighted counts are additive along a disjoint union of prime sets. -/
theorem primeTheta_union (hST : Disjoint S T) (x : ℝ) :
    primeTheta K (S ∪ T) x = primeTheta K S x + primeTheta K T x := by
  rw [primeTheta, Set.indicator_union_of_disjoint hST]
  exact summatory_add _ _ _ x



/-- Chebyshev's trivial comparison: each counted prime contributes at most `log x`. -/
theorem primeTheta_le_primeCount_mul_log (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x ≤ primeCount K S x * Real.log x := by
  rw [primeTheta_apply, primeCount_apply, Finset.sum_mul]
  refine Finset.sum_le_sum fun v hv ↦ ?_
  rw [mem_normLE] at hv
  by_cases hS : v ∈ S
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS, Pi.one_apply, one_mul]
    exact Real.log_le_log (absNorm_asIdeal_real_pos v) hv
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS, zero_mul]



open Asymptotics Filter in
/-- **Primes counted below the prime-ideal-theorem order carry negligible weight.** Chebyshev's
comparison spends one factor of `log x` per counted prime, so a count of `o(x / log x)` gives a
weighted sum of `o(x)`.

Stated for an arbitrary prime set, since the argument uses nothing about which primes are counted;
`TauCeti.primeTheta_higherDegreePrimes_isLittleO` is the residue-degree instance. -/
theorem primeTheta_isLittleO_of_primeCount_isLittleO
    (h : primeCount K S =o[atTop] fun x : ℝ ↦ x / Real.log x) :
    primeTheta K S =o[atTop] fun x : ℝ ↦ x := by
  have hlog : ∀ᶠ x : ℝ in atTop, Real.log x ≠ 0 :=
    (eventually_gt_atTop (1 : ℝ)).mono fun _ hx ↦ (Real.log_pos hx).ne'
  have hmul : (fun x : ℝ ↦ primeCount K S x * Real.log x) =o[atTop] fun x : ℝ ↦ x := by
    simpa [mul_comm] using (isLittleO_mul_iff_isLittleO_div hlog).2 h
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (.of_forall fun x ↦ ?_)) hmul
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (primeTheta_nonneg _ _)]
  exact (primeTheta_le_primeCount_mul_log _ x).trans (le_abs_self _)







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





/-! ### Counting the primes of residue degree above one -/



/-- The primes of residue degree above one and norm at most `x` number `O(√x)`. -/
theorem primeCount_higherDegreePrimes_isBigO :
    primeCount K (higherDegreePrimes K) =O[atTop] Real.sqrt := by
  refine .of_bound (Module.finrank ℚ K) (.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (primeCount_nonneg (higherDegreePrimes K) x),
    Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  exact primeCount_higherDegreePrimes_le x

private theorem sqrt_isLittleO_div_log : Real.sqrt =o[atTop] fun x ↦ x / Real.log x := by
  have hne : ∀ᶠ x in atTop, x / Real.log x = 0 → √x = 0 := by
    filter_upwards [eventually_gt_atTop 2] with x hx h
    exact absurd h (div_ne_zero (by linarith) (Real.log_pos (by linarith)).ne')
  rw [isLittleO_iff_tendsto' hne]
  -- The quotient is `log x / √x`, which tends to `0` because `log =o[atTop] x ^ (1 / 2)`.
  have hquot : (fun x : ℝ ↦ √x / (x / Real.log x)) =ᶠ[atTop] fun x : ℝ ↦ Real.log x / √x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hsx : √x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    calc √x / (x / Real.log x) = √x * Real.log x / x := div_div_eq_mul_div _ _ _
      _ = √x * Real.log x / (√x * √x) := by rw [Real.mul_self_sqrt hx.le]
      _ = Real.log x / √x := mul_div_mul_left _ _ hsx
  have h0 : Tendsto (fun x : ℝ ↦ Real.log x / √x) atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  exact Tendsto.congr' hquot.symm h0

/-- The primes of residue degree above one and norm at most `x` number `o(x / log x)`.  The
comparison is with the explicit function `x / log x`, not with the full prime count `π_K(x)`;
`x / log x` is the order of magnitude the prime ideal theorem gives for `π_K`, but that theorem
is not available here, so this is not a statement of natural density zero. -/
theorem primeCount_higherDegreePrimes_isLittleO :
    primeCount K (higherDegreePrimes K) =o[atTop] fun x ↦ x / Real.log x :=
  primeCount_higherDegreePrimes_isBigO.trans_isLittleO sqrt_isLittleO_div_log

/-- **The primes of residue degree above one carry a negligible weight.** Their contribution to
`ϑ_K` is `o(x)`.

This is the count `o(x / log x)` above, weighted by Chebyshev's `log x` per prime. It is the
estimate a contraction between two number fields discards: the norms satisfy
`𝔑_{E/ℚ}𝔓 = (𝔑_{K/ℚ}𝔭)^{f(𝔓/𝔭)}`, so a term of `ϑ` moves to a different value of `n` unless the
relative residue degree is one, and `f(𝔓/𝔭) ≥ 2` forces `f(𝔓/p) ≥ 2`, which is what this absolute
statement covers. -/
theorem primeTheta_higherDegreePrimes_isLittleO (K : Type*) [Field K] [NumberField K] :
    primeTheta K (higherDegreePrimes K) =o[atTop] fun x : ℝ ↦ x :=
  primeTheta_isLittleO_of_primeCount_isLittleO primeCount_higherDegreePrimes_isLittleO

/-! ### Convergence of the prime Dirichlet series over the degree-above-one primes -/








/-! ### All height-one primes -/







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

/-- Chebyshev's `ϑ` never exceeds `ψ`. -/
theorem primeTheta_le_primePsi (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x ≤ primePsi K S x := by
  rw [← sub_nonneg, primePsi_sub_primeTheta]
  exact primePowerSummatory_nonneg K _
    (fun A ↦ Set.indicator_nonneg (fun A _ ↦ higherPrimePowerWeight_nonneg A) A) x

/-! ### Removing the higher prime powers -/









open Asymptotics in
/-- **A finite set of primes is `O(log x)` for `ψ`**, the asymptotic form of the bound above. -/
theorem primePsi_isBigO_log_of_finite (hS : S.Finite) :
    primePsi K S =O[atTop] Real.log := by
  refine IsBigO.of_bound S.ncard ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (primePsi_nonneg _ _),
    abs_of_nonneg (Real.log_nonneg hx)]
  exact primePsi_le_ncard_mul_log hS hx

open Asymptotics in
/-- **A finite set of primes is negligible for `ψ`**, the form the total discard estimate sums. -/
theorem primePsi_isLittleO_of_finite (hS : S.Finite) :
    primePsi K S =o[atTop] fun x : ℝ ↦ x :=
  (primePsi_isBigO_log_of_finite hS).trans_isLittleO Real.isLittleO_log_id_atTop







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
# Primes above a set of primes, and the Selmer group relative to them

For an injective algebra map of commutative rings `R → B` with `B` Dedekind, only finitely
many nonzero prime ideals of `B` lie over a given nonzero prime `v` of `R`. This does not
require integrality or a Dedekind hypothesis on `R`.

For domains `R` and `B` with `B` integral over `R`, contraction defines
`HeightOneSpectrum.under R`. For a set `S` of primes of `R`,
`IsDedekindDomain.HeightOneSpectrum.primesAbove R B S` is its preimage under contraction.
When `B` is Dedekind and the algebra map is injective, this preimage is finite whenever `S` is.
The Selmer group of the fraction field of `B` relative to these primes is
`IsDedekindDomain.selmerGroupAbove R B L S n`, Mathlib's `L⟮primesAbove R B S, n⟯`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.primesAbove`: the primes of `B` above a set of primes
  of `R`, as a preimage under `HeightOneSpectrum.under`.
* `IsDedekindDomain.selmerGroupAbove`: the `n`-Selmer group of `L` relative to the primes of `B`
  above `S`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.liesOver_under`: the `LiesOver` instance relating a prime
  to its contraction, which the `under`-indexed results downstream need.
* `IsDedekindDomain.HeightOneSpectrum.under_under`: contraction through a tower agrees with
  direct contraction.
* `IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff`: `w` lies above `S` iff
  `HeightOneSpectrum.under R w ∈ S`.
* `IsDedekindDomain.HeightOneSpectrum.primesAbove_finite`: finitely many primes lie above a
  finite set.
* `IsDedekindDomain.HeightOneSpectrum.tendsto_under_cofinite`: consequently, contraction tends to
  the cofinite filter along the cofinite filter;
  `IsDedekindDomain.HeightOneSpectrum.tendsto_under_cofinite_of_isFractionRing` is the variant
  for rings mapping compatibly to a common nontrivial algebra over a fraction field.
* `IsDedekindDomain.HeightOneSpectrum.finite_liesOver`: finitely many height one primes lie over
  a given one.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, at commit `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `DedekindDomain`. The source carries its own
`HeightOneSpectrum.below`; at our Mathlib pin that map is `HeightOneSpectrum.under`, which is
used here instead.

The source is written against Lean `v4.32.0`; this is a forward port.
-/

 section

namespace IsDedekindDomain

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [Algebra R B]

namespace HeightOneSpectrum

section IsDomain

variable [IsDomain R] [IsDomain B] [Algebra.IsIntegral R B]



section UnderTower

variable {A C : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
  [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
  [Algebra.IsIntegral A R] [Algebra.IsIntegral R C]



end UnderTower



/-- A prime of `B` lies above `S` exactly when its contraction to `R` lies in `S`. -/
@[simp]
lemma mem_primesAbove_iff (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ under R w ∈ S := Iff.rfl





end IsDomain

section

variable {R B}

variable (B) [FaithfulSMul R B]



end







end HeightOneSpectrum

variable [IsDomain R] [IsDedekindDomain B] [Algebra.IsIntegral R B]







end IsDedekindDomain

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







/-- A member of `frobeniusPrimeSet K L C` is unramified in `L`. -/
theorem isUnramifiedAt_of_mem_frobeniusPrimeSet {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} (h : 𝔭 ∈ frobeniusPrimeSet K L C)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) Q :=
  (mem_frobeniusPrimeSet_iff.mp h).elim fun hur _ ↦ hur Q

/-- No ramified prime carries an Artin class: the fibres avoid `ramifiedPrimes K L`. -/
theorem frobeniusPrimeSet_subset_compl_ramifiedPrimes (C : ConjClasses (L ≃ₐ[K] L)) :
    frobeniusPrimeSet K L C ⊆ (↑(ramifiedPrimes K L))ᶜ := fun 𝔭 h hmem ↦
  (mem_ramifiedPrimes_iff 𝔭).mp (Finset.mem_coe.mp hmem) fun Q _ _ ↦
    isUnramifiedAt_of_mem_frobeniusPrimeSet h Q







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

























/-- `frobeniusTheta` as an explicit sum over the inclusive prime carrier. -/
theorem frobeniusTheta_apply (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    frobeniusTheta K L C x =
      ∑ 𝔭 ∈ primesLE K x, (frobeniusPrimeSet K L C).indicator
        (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) 𝔭 := by
  rw [frobeniusTheta, primeTheta_apply]



























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

/-- The higher prime powers make a nonnegative contribution to Frobenius `ψ`. -/
theorem frobeniusTheta_le_frobeniusPsi (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    frobeniusTheta K L C x ≤ frobeniusPsi K L C x := by
  rw [← sub_nonneg, frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory]
  exact primePowerSummatory_nonneg K _
    (fun A ↦ Set.indicator_nonneg (fun A _ ↦ higherPrimePowerWeight_nonneg A) A) x



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
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The primes of a number field above those ramifying in another

For an extension `L / K` of number fields and a further number field `E` over `K`, this file
collects the height-one primes of `𝓞 E` whose contraction to `𝓞 K` ramifies in `L`. There are
finitely many, so they form a `Finset`.

`E` is unrelated to `L`: the condition constrains the prime of `K` below, and says nothing about
how the prime behaves in `L / E`.

## Main definitions

* `NumberField.Chebotarev.primesAboveRamifiedPrimes`: the finite set of height-one primes of
  `𝓞 E` lying above `ramifiedPrimes K L`.

## Main results

* `NumberField.Chebotarev.mem_primesAboveRamifiedPrimes_iff`: the defining condition for
  membership.
* `NumberField.Chebotarev.under_mem_primesAboveRamifiedPrimes_of_not_isUnramifiedAt`: a prime
  below a ramified prime in a tower satisfies the defining condition.
* `NumberField.Chebotarev.under_mem_primesAboveRamifiedPrimes_iff_inertia_ne_bot`: in a
  Galois tower, membership of the contraction is equivalent to nontrivial inertia upstairs.

## Comparison with ramification in `L / E`

Nothing here assumes `E` embeds in `L`, so in general there is no ramification in `L / E` to
compare against: membership is a condition on the prime of `K` below `𝔓`, and nothing else.

When a compatible tower `K → E → L` does exist, the two conditions are still not the same one.
Ramification indices multiply along a tower, `e(Q/𝔭) = e(Q/𝔓) · e(𝔓/𝔭)`, so a prime of `E`
ramifying in `L / E` always lies in this set. The inclusion can be strict, and that is why the
condition is imposed below rather than on `L / E`.

For example, take `K = ℚ` and `L = ℚ(∛2, ζ₃)`, so that `Gal(L/K) ≅ S₃`; let `E = ℚ(∛2)`, the field
fixed by a transposition, and let `p = 2`. The inertia group at a prime `Q` of `L` above `2` is the
cyclic group of order three, so `e(Q/2) = 3` while `e(Q/𝔓) = 1`: all of the ramification,
`e(𝔓/2) = 3`, happens below `E`. So `𝔓` is unramified in `L / E` and yet lies above a prime
ramifying in `L / K` — a witness that the inclusion is strict here.

## References

Adapted from `ramifiedBelow_finite` in `CebotarevDensity/FixedFieldDensity.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) on branch `development` at commit
`8575c9df1ae0a61120ab5c964c7911414254bec7`, where the set appears for `E` the fixed field of a
cyclic subgroup of `Gal(L/K)`.
-/

 section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable (K L E : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field E] [NumberField E] [Algebra K E]



variable {K L E}

/-- The defining condition for membership in `primesAboveRamifiedPrimes`: the prime of `𝓞 K`
below `𝔓` ramifies in `L`. -/
@[simp]
theorem mem_primesAboveRamifiedPrimes_iff (𝔓 : HeightOneSpectrum (𝓞 E)) :
    𝔓 ∈ primesAboveRamifiedPrimes K L E ↔ 𝔓.under (𝓞 K) ∈ ramifiedPrimes K L :=
  (Set.Finite.mem_toFinset _).trans (HeightOneSpectrum.mem_primesAbove_iff _ _ _ _)





end NumberField.Chebotarev

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
# Negligible terms in Frobenius prime counting

Weighted crossing arguments bound the error incurred when passing from a Frobenius prime-power sum
to a prime sum of residue degree one by three functions. These account for higher prime powers in
the chosen Frobenius class and use unrestricted sums to majorize the contributions from primes of
absolute residue degree above one and from a finite exceptional set. Each majorant is `o(x)` for a
different reason. This file records that their sum is `o(x)`.

## Main result

* `NumberField.Chebotarev.frobeniusDiscard_isLittleO`: the sum of three majorants for the discard
  error is negligible compared with `x`.
-/

 section

namespace NumberField.Chebotarev

open Filter TauCeti
open scoped Asymptotics NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- The sum of three majorants for the error incurred when a Frobenius prime-power sum is restricted
to residue-degree-one primes outside a finite exceptional set is `o(x)`.

The first summand is the higher-prime-power contribution in the Frobenius fibre. The other two are
unrestricted weighted sums over all primes of absolute residue degree greater than one and all
prime powers based at an exceptional prime.
-/
theorem frobeniusDiscard_isLittleO (C : ConjClasses (L ≃ₐ[K] L))
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (fun x : ℝ ↦ frobeniusPsi K L C x - frobeniusTheta K L C x +
        primeTheta K (higherDegreePrimes K) x +
        primePsi K (T : Set (HeightOneSpectrum (𝓞 K))) x) =o[atTop] fun x : ℝ ↦ x :=
  ((frobeniusPsi_sub_frobeniusTheta_isLittleO C).add
    (primeTheta_higherDegreePrimes_isLittleO K)).add
      (primePsi_isLittleO_of_finite T.finite_toSet)

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
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

open _root_.TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Grouping by the prime below: a set of primes of `L ^ <sigma>` consisting exactly of the
members of the relative fiber of `sigma` lying over the Frobenius fiber of `sigma` has
`primeTheta` equal to the fixed-field multiplicity times `frobeniusTheta`. -/
private theorem NumberField.Chebotarev.primeTheta_eq_mul_frobeniusTheta_of_forall_mem_iff (sigma : L ≃ₐ[K] L)
    {S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma))))}
    (hS : ∀ P, P ∈ S ↔
      P ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
          (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) ∧
        P.under (𝓞 K) ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet K L (_root_.ConjClasses.mk sigma)) (x : ℝ) :
    _root_.TauCeti.primeTheta ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) S x =
      ((_root_.Nat.card (L ≃ₐ[K] L) /
          (_root_.Nat.card (_root_.ConjClasses.mk sigma).carrier * _root_.orderOf sigma) : ℕ) : ℝ) *
        _root_.NumberField.Chebotarev.frobeniusTheta K L (_root_.ConjClasses.mk sigma) x := by
  classical
  -- Every member of `S` has residue degree one over `K`, hence the norm of the prime below.
  have hnorm : ∀ P ∈ S, _root_.Ideal.absNorm P.asIdeal = _root_.Ideal.absNorm (P.under (𝓞 K)).asIdeal := by
    intro P hPS
    obtain ⟨hP, hp⟩ := (hS P).mp hPS
    have hdeg := (_root_.NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet sigma hP fun h ↦
      _root_.NumberField.Chebotarev.frobeniusPrimeSet_subset_compl_ramifiedPrimes _ hp (Finset.mem_coe.mpr h)).mpr hp
    have : P.asIdeal.LiesOver (P.under (𝓞 K)).asIdeal := ⟨_root_.IsDedekindDomain.HeightOneSpectrum.under_asIdeal _ P⟩
    rw [← _root_.Ideal.absNorm_pow_inertiaDeg (P.under (𝓞 K)).asIdeal P.asIdeal, hdeg, _root_.pow_one]
  rw [_root_.TauCeti.primeTheta_apply, _root_.NumberField.Chebotarev.frobeniusTheta_apply]
  simp only [_root_.Set.indicator_apply]
  rw [← _root_.Finset.sum_filter, ← _root_.Finset.sum_filter, _root_.Finset.mul_sum]
  refine (_root_.Finset.sum_fiberwise_of_maps_to (g := fun P ↦ P.under (𝓞 K)) ?_ _).symm.trans
    (_root_.Finset.sum_congr _root_.rfl fun p hp ↦ ?_)
  · intro P hP
    simp only [_root_.Finset.mem_filter, _root_.TauCeti.mem_normLE] at hP ⊢
    exact ⟨hnorm P hP.2 ▸ hP.1, ((hS P).mp hP.2).2⟩
  simp only [_root_.Finset.mem_filter, _root_.TauCeti.mem_normLE] at hp
  rw [_root_.Finset.sum_congr _root_.rfl fun P hP ↦ by
    simp only [_root_.Finset.mem_filter] at hP
    rw [hnorm P hP.1.2, hP.2], _root_.Finset.sum_const, _root_.nsmul_eq_mul]
  -- The primes of `E` counted over `p` are exactly those of `fixedField_frobenius_fiber_card`.
  rw [← _root_.NumberField.Chebotarev.fixedField_frobenius_fiber_card _ sigma _root_.ConjClasses.mem_carrier_mk p hp.2,
    ← _root_.Nat.card_eq_finsetCard]
  refine _root_.congrArg (· * _) (_root_.congrArg _root_.Nat.cast (_root_.Nat.card_congr
    (_root_.Equiv.subtypeEquivRight fun P ↦ ?_)))
  simp only [_root_.Finset.mem_filter, _root_.TauCeti.mem_normLE]
  refine ⟨fun ⟨⟨_, hPS⟩, hPp⟩ ↦ ⟨hPp, ((hS P).mp hPS).1⟩, fun ⟨hPp, hP⟩ ↦ ?_⟩
  have hPS : P ∈ S := (hS P).mpr ⟨hP, hPp ▸ hp.2⟩
  exact ⟨⟨by rw [hnorm P hPS, hPp]; exact hp.1, hPS⟩, hPp⟩

/-- **The exact residue-degree-one contraction of Frobenius `ϑ`.** Let `sigma` represent `C` and
let `E = L ^ <sigma>`.  Sum `log N 𝔓` over the primes `𝔓` of `E` of norm at most `x` whose relative
Artin class in `L / E` is represented by `sigma.toFixedFieldAlgEquiv`, that do not lie above a prime
of `K` ramified in `L`, and that have residue degree one over `K`.  The result is exactly

```text
(#Gal(L/K) / (#C * orderOf sigma)) * frobeniusTheta K L C x.
```

The natural-number division is exact by `ConjClasses.card_carrier_mul_orderOf_dvd`. -/
theorem NumberField.Chebotarev.primeTheta_fixedField_eq_mul_frobeniusTheta (C : _root_.ConjClasses (L ≃ₐ[K] L))
    (sigma : L ≃ₐ[K] L) (hsigma : sigma ∈ C.carrier) (x : ℝ) :
    _root_.TauCeti.primeTheta ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma))
        {P | P ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
            (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) ∧
          P ∉ _root_.NumberField.Chebotarev.primesAboveRamifiedPrimes K L ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) ∧
          P.asIdeal.inertiaDeg (𝓞 K) = 1} x =
      ((_root_.Nat.card (L ≃ₐ[K] L) / (_root_.Nat.card C.carrier * _root_.orderOf sigma) : ℕ) : ℝ) *
        _root_.NumberField.Chebotarev.frobeniusTheta K L C x := by
  obtain rfl : _root_.ConjClasses.mk sigma = C := ConjClasses.mem_carrier_iff_mk_eq.mp hsigma
  refine _root_.NumberField.Chebotarev.primeTheta_eq_mul_frobeniusTheta_of_forall_mem_iff sigma (fun P ↦ ?_) x
  rw [_root_.Set.mem_ofPred_eq, _root_.NumberField.Chebotarev.mem_primesAboveRamifiedPrimes_iff]
  refine ⟨fun ⟨hP, hram, hdeg⟩ ↦
    ⟨hP, (_root_.NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet sigma hP hram).mp hdeg⟩,
    fun ⟨hP, hp⟩ ↦ ?_⟩
  have hram : P.under (𝓞 K) ∉ _root_.NumberField.Chebotarev.ramifiedPrimes K L := fun h ↦
    _root_.NumberField.Chebotarev.frobeniusPrimeSet_subset_compl_ramifiedPrimes _ hp (Finset.mem_coe.mpr h)
  exact ⟨hP, hram, (_root_.NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet sigma hP hram).mpr hp⟩

omit [_root_.NumberField L] [_root_.IsGalois K L] in
/-- **What the exact contraction discards.** Removing from `S` the primes that avoid `T` and have
residue degree one over `K` leaves only primes of higher degree together with primes of `T`: a
prime not in `T` and not of degree one has degree at least two.

Nothing here is about fixed fields: `E` is any number field over `K`. The contraction below
instantiates it at `L ^ <sigma>`. -/
private theorem NumberField.Chebotarev.sdiff_setOf_inertiaDeg_eq_one_subset {E : Type*} [_root_.Field E] [_root_.NumberField E]
    [_root_.Algebra K E] (S T : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :
    S \ {P | P ∈ S ∧ P ∉ T ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1} ⊆
      _root_.TauCeti.higherDegreePrimes E ∪ (T \ _root_.TauCeti.higherDegreePrimes E) := by
  rw [_root_.Set.union_sdiff_self]
  intro P ⟨hPS, hPA⟩
  by_cases hPT : P ∈ T
  · exact _root_.Or.inr hPT
  · exact _root_.Or.inl (_root_.TauCeti.mem_higherDegreePrimes_of_one_lt_inertiaDeg
      (_root_.lt_of_le_of_ne (_root_.Ideal.inertiaDeg_pos P.asIdeal (𝓞 K))
        fun h ↦ hPA ⟨hPS, hPT, h.symm⟩))

/-- **The weighted contraction of Frobenius `ψ`.** Let `sigma` represent `C` and let
`E = L ^ <sigma>`.  The relative Frobenius `ψ` of `sigma` in `L / E` is the fixed-field
multiplicity `#Gal(L/K) / (#C * orderOf sigma)` times `frobeniusPsi K L C`, up to `o(x)`.

Unlike `primeTheta_fixedField_eq_mul_frobeniusTheta`, this is not an identity: the error collects
the prime powers with exponent at least two on both sides, the relative primes of residue degree
above one over `K`, and the relative primes above `ramifiedPrimes K L`. -/
theorem solution (C : _root_.ConjClasses (L ≃ₐ[K] L))
    (sigma : L ≃ₐ[K] L) (hsigma : sigma ∈ C.carrier) :
    (fun x : ℝ ↦
      _root_.NumberField.Chebotarev.frobeniusPsi ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
          (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) x -
        ((_root_.Nat.card (L ≃ₐ[K] L) / (_root_.Nat.card C.carrier * _root_.orderOf sigma) : ℕ) : ℝ) *
          _root_.NumberField.Chebotarev.frobeniusPsi K L C x) =o[_root_.Filter.atTop] fun x : ℝ ↦ x := by
  set E := _root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)
  set d : ℝ := ((_root_.Nat.card (L ≃ₐ[K] L) / (_root_.Nat.card C.carrier * _root_.orderOf sigma) : ℕ) : ℝ)
  set T := _root_.NumberField.Chebotarev.primesAboveRamifiedPrimes K L E
  set S := _root_.NumberField.Chebotarev.frobeniusPrimeSet E L (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv)
  set A : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :=
    {P | P ∈ S ∧ P ∉ T ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1}
  -- The relative primes outside the exact contraction have higher degree or lie in `T`.
  have hsub : S \ A ⊆ _root_.TauCeti.higherDegreePrimes E ∪ (T \ _root_.TauCeti.higherDegreePrimes E) :=
    _root_.NumberField.Chebotarev.sdiff_setOf_inertiaDeg_eq_one_subset S T
  -- `u` is everything discarded on the `E` side; it lies between `0` and the discard majorant.
  set u : ℝ → ℝ := fun x ↦ _root_.NumberField.Chebotarev.frobeniusPsi E L (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) x -
    _root_.NumberField.Chebotarev.frobeniusTheta E L (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) x + _root_.TauCeti.primeTheta E (S \ A) x
  have hu : u =o[_root_.Filter.atTop] fun x : ℝ ↦ x := by
    refine (_root_.Asymptotics.isBigO_of_le _ fun x ↦ ?_).trans_isLittleO
      (_root_.NumberField.Chebotarev.frobeniusDiscard_isLittleO (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) T)
    have h0 := sub_nonneg.mpr (_root_.NumberField.Chebotarev.frobeniusTheta_le_frobeniusPsi
      (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) x)
    have hB : _root_.TauCeti.primeTheta E (S \ A) x ≤ _root_.TauCeti.primeTheta E (_root_.TauCeti.higherDegreePrimes E) x + _root_.TauCeti.primePsi E T x := by
      refine (_root_.TauCeti.primeTheta_mono_set hsub x).trans ?_
      rw [_root_.TauCeti.primeTheta_union _root_.Set.disjoint_sdiff_right]
      exact _root_.add_le_add_right ((_root_.TauCeti.primeTheta_mono_set _root_.Set.sdiff_subset x).trans
        (_root_.TauCeti.primeTheta_le_primePsi _ x)) _
    rw [_root_.Real.norm_of_nonneg (_root_.add_nonneg h0 (_root_.TauCeti.primeTheta_nonneg _ x)), _root_.Real.norm_of_nonneg]
    · linarith
    · linarith [_root_.TauCeti.primeTheta_nonneg (_root_.TauCeti.higherDegreePrimes E) x, _root_.TauCeti.primeTheta_nonneg (S \ A) x]
  refine ((hu.sub ((_root_.NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_isLittleO C).const_mul_left d))).congr
    (fun x ↦ ?_) fun _ ↦ _root_.rfl
  -- Split the relative `ϑ` into the exact contraction and the discarded primes.
  have hsplit : _root_.NumberField.Chebotarev.frobeniusTheta E L (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) x =
      d * _root_.NumberField.Chebotarev.frobeniusTheta K L C x + _root_.TauCeti.primeTheta E (S \ A) x := by
    rw [_root_.NumberField.Chebotarev.frobeniusTheta_apply, ← _root_.TauCeti.primeTheta_apply,
      ← _root_.NumberField.Chebotarev.primeTheta_fixedField_eq_mul_frobeniusTheta C sigma hsigma x,
      ← _root_.TauCeti.primeTheta_union _root_.Set.disjoint_sdiff_right,
      _root_.Set.union_sdiff_cancel fun P hP ↦ hP.1]
  simp only [u, hsplit]
  ring





end NumberField.Chebotarev

end
end
