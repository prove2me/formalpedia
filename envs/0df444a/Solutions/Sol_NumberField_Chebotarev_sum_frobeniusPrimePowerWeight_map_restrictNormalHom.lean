-- Prove2me | solution 1 for NumberField.Chebotarev.sum_frobeniusPrimePowerWeight_map_restrictNormalHom
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:41:23.150906+00:00
-- url     : https://prove2.me/submissions/f1cd0120-e7b9-40e1-b085-52dbe15eabcb

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_RamificationInertia_Tower
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
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
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_NumberField_artinSymbol_map_restrictNormalHom

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









/-- The image of the class of `a` under `ConjClasses.map f` is the class of `f a`. -/
-- Mathlib defines `ConjClasses.map` as a `Quotient.lift` and provides no computation rule for it,
-- so this reduction is stated here once and every naturality statement below rewrites with it.
@[simp]
theorem map_mk {N : Type*} [Monoid N] (f : M →* N) (a : M) :
    ConjClasses.map f (ConjClasses.mk a) = ConjClasses.mk (f a) := rfl

/-- Powering a conjugacy class is natural in the monoid. -/
@[simp]
theorem map_pow {N : Type*} [Monoid N] (f : M →* N) (C : ConjClasses M) (j : ℕ) :
    ConjClasses.map f (C ^ j) = ConjClasses.map f C ^ j := by
  obtain ⟨a, rfl⟩ := ConjClasses.exists_rep C
  -- Every reduction here is named rather than left to definitional unfolding: `map_mk` computes
  -- the map on representatives, after which `mk_pow` handles both powers and `map_pow` finishes
  -- in `N`.
  rw [mk_pow, map_mk, map_mk, mk_pow, _root_.map_pow]





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
# The primes of a number field ramifying in a finite extension

For an extension `L / K` of number fields, a height-one prime `𝔭` of `𝓞 K` is *ramified in `L`*
when some prime `Q` of `𝓞 L` lying over it is ramified, i.e. when

`¬ ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q`.

Only finitely many `𝔭` are ramified, because each of them is the contraction of a prime dividing
the different ideal `differentIdeal (𝓞 K) (𝓞 L)`, which is nonzero and so has finitely many prime
divisors. That finiteness is what lets the ramified primes be packaged as a `Finset`, which is the
form Chebotarev's exceptional set is used in: the density statements discard `ramifiedPrimes K L`
and argue about the complement.

The ramification condition is spelled out with Mathlib's `Algebra.IsUnramifiedAt` rather than
wrapped in a named predicate, matching how the roadmap states it. A `Prop`-valued abbreviation for
"`𝔭` is unramified in `L`" would duplicate `Algebra.IsUnramifiedIn`.

## Main definitions

* `NumberField.Chebotarev.ramifiedPrimes`: the finite set of height-one primes of `𝓞 K` that
  ramify in `L`.

## Main results

* `NumberField.Chebotarev.mem_ramifiedPrimes_iff`: the defining condition for membership.
* `NumberField.Chebotarev.under_notMem_ramifiedPrimes_iff_isUnramifiedAt`: in a Galois
  extension, unramifiedness can be tested at one prime above the base prime.
* `NumberField.Chebotarev.ramifiedPrimes_subset_ramifiedPrimes`: for a tower `K ⊆ L ⊆ M`, every
  prime of `K` ramifying in `L` also ramifies in `M`.

## Relation to the absolute `NumberField.ramifiedPrimes`

Every name used here already exists one namespace up, and this is deliberate rather than an
oversight. `TauCeti/NumberTheory/NumberField/RamifiedPrimes.lean` carries

* `NumberField.ramifiedPrimes (K) : Set ℕ`, the *rational* primes ramifying in `K`,
* `@[simp] NumberField.mem_ramifiedPrimes_iff`, proved by `Iff.rfl`, and
* `NumberField.finite_ramifiedPrimes`,

i.e. the same short names, in the same shape. They are kept apart rather than unified:

* They are the same *shape* — "not `Algebra.IsUnramifiedIn` the top ring at an ideal of the base"
  — but at different bases. The absolute one is `ℤ`-to-`𝓞 K`; this one is `𝓞 K`-to-`𝓞 L`. Neither
  is an instance of the other without also transporting the carrier.
* The carriers genuinely differ: `Set ℕ` against `Finset (HeightOneSpectrum (𝓞 K))`. For `K = ℚ`
  the two agree only through `𝓞 ℚ ≃ ℤ` and `HeightOneSpectrum ℤ ≃` the rational primes, and
  neither identification is definitional.
* Generalising the absolute version instead would change its carrier, and Tau Ceti keeps no
  compatibility shims, so every use would have to move in this PR — ten files on `main` reference
  that API, seven of them under `Multiquadratic/`. Its `Set ℕ` packaging is, in its own docstring,
  "the form in which `t` is counted" for genus theory.

Two consequences to be aware of when using this file. First, `NumberField.Chebotarev` is nested
inside `NumberField`, so within it a bare `ramifiedPrimes` or `mem_ramifiedPrimes_iff` resolves to
the declaration here and shadows the absolute one; a `Chebotarev` file that also wants the
absolute notion must write `_root_.NumberField.ramifiedPrimes`. (The finiteness lemma is private,
so its name collides only inside this file.) Second, both `_iff` lemmas are
`@[simp]`, but their left-hand sides head-match on different types — membership in a `Set ℕ`
against membership in a `Finset (HeightOneSpectrum (𝓞 K))` — so `simp` never has to choose
between them.

## References

Adapted from `finite_ramifiedIn` in `CebotarevDensity/Frobenius.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, where the statement is a
`Set.Finite` over `Ideal (𝓞 K)` phrased through a source-local unramifiedness predicate. The
covering argument through the different ideal is the source's; the carrier is the roadmap's.
-/

 section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]





variable {K L}





variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- **Ramification ascends a tower.** For number fields `K ⊆ L ⊆ M`, a prime of `K` that ramifies
in `L` also ramifies in `M`. Equivalently, a prime unramified in `M` is unramified in every
intermediate field. -/
theorem ramifiedPrimes_subset_ramifiedPrimes : ramifiedPrimes K L ⊆ ramifiedPrimes K M := by
  intro 𝔭
  contrapose
  rw [mem_ramifiedPrimes_iff, mem_ramifiedPrimes_iff, not_not, not_not]
  intro hur P _ _
  exact TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn (S := 𝓞 M) hur P

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

/-- With an unramifiedness proof fixed, membership in the powered Frobenius fibre is the stated
equality of conjugacy classes. In particular, membership is independent of that proof. -/
theorem mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq {A : IdealPrimePower K}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (C : ConjClasses (L ≃ₐ[K] L)) :
    A ∈ frobeniusPrimePowerSet K L C ↔
      artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hur, h⟩⟩

-- Not `@[simp]`: `mem_frobeniusPrimePowerSet_iff` together with `primePowerBase_ofPrime`,
-- `primePowerExponent_ofPrime` and `ConjClasses.pow_one` already rewrites the left-hand side.




/-- A prime power in the `C`-fibre has weight `log N(𝔭)`. -/
@[simp]
theorem frobeniusPrimePowerWeight_of_mem {C : ConjClasses (L ≃ₐ[K] L)}
    {A : IdealPrimePower K} (hA : A ∈ frobeniusPrimePowerSet K L C) :
    frobeniusPrimePowerWeight K L C A = primePowerWeight A := by
  rw [frobeniusPrimePowerWeight, Set.indicator_of_mem hA]

/-- A prime power whose powered Artin class is `C` contributes its full logarithmic weight.
This exposes the power in the filter: the unpowered Artin class need not equal `C`. -/
theorem frobeniusPrimePowerWeight_of_artinSymbol_pow_eq {A : IdealPrimePower K}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) {C : ConjClasses (L ≃ₐ[K] L)}
    (hC : artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C) :
    frobeniusPrimePowerWeight K L C A = primePowerWeight A :=
  frobeniusPrimePowerWeight_of_mem
    ((mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hur C).mpr hC)

/-- A prime power outside the `C`-fibre has weight zero. -/
@[simp]
theorem frobeniusPrimePowerWeight_of_notMem {C : ConjClasses (L ≃ₐ[K] L)}
    {A : IdealPrimePower K} (hA : A ∉ frobeniusPrimePowerSet K L C) :
    frobeniusPrimePowerWeight K L C A = 0 :=
  Set.indicator_of_notMem hA _













































-- The powered filter is exercised here: this is the term a definition filtering on
-- `artinSymbol 𝔭 = C` alone would lose. The order-four configuration is not vacuous —
-- `ConjClasses.mk_ne_mk_of_orderOf_ne` separates the two classes for *every* element of order
-- four, its square having order two, and the cyclic group of order four realises such an element
-- concretely.




















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
# Frobenius `ψ` along a normal subextension

Let `K ⊆ M ⊆ L` be number fields with `L / K` and `M / K` Galois. Restriction to `M` is a group
homomorphism `Gal(L/K) → Gal(M/K)`, it carries the Artin class of a prime `𝔭` of `𝓞 K` to the
Artin class of `𝔭` for `M / K` with no power taken
(`NumberField.artinSymbol_map_restrictNormalHom`), and it commutes with powers of conjugacy
classes. So a prime power `𝔭 ^ j` counted by `frobeniusPsi K L D` for a class `D` of `Gal(L/K)` is
counted by `frobeniusPsi K M C` for the single class `C = ConjClasses.map _ D`, and the classes `D`
lying over a fixed `C` contribute to it disjointly.

This file records that refinement. Pointwise, the Frobenius weights of the classes over `C` add up
to the Frobenius weight of `C` itself, except at prime powers based at a prime ramifying in `L`,
where the upper weights all vanish while the lower one need not. Summing over prime powers, any
family of distinct classes over `C` gives a lower bound for `frobeniusPsi K M C`, and the full
family misses only the finitely many primes of `ramifiedPrimes K L`, hence accounts for
`frobeniusPsi K M C` up to `O(log x)`.

The lower bound is the shape the cyclotomic crossing consumes: over the compositum `M(μ_q)` of `M`
with an auxiliary cyclotomic field, the classes of the tagged elements `(σ, τ)` for distinct `τ`
are distinct classes over the class of `σ`, so the weighted asymptotics of their fibres add up to a
lower bound for the weighted asymptotics of the fibre of `σ`.

There is no companion upper bound for a proper subfamily, and none is needed: the crossing closes
by summing the lower bounds over all of `Gal(M/K)` against `ψ_M`, which
`NumberField.Chebotarev.primePsi_univ_sub_sum_frobeniusPsi_isBigO_log` supplies.

## Main results

* `NumberField.Chebotarev.sum_frobeniusPrimePowerWeight_map_restrictNormalHom`: at a single prime
  power, the Frobenius weights of the classes of `Gal(L/K)` over `C` add up to the Frobenius weight
  of `C`, unless the base ramifies in `L`, in which case they add up to `0`.
* `NumberField.Chebotarev.sum_frobeniusPsi_le_frobeniusPsi`: the Frobenius `ψ` functions of any
  finite family of distinct classes over `C` add up to at most `frobeniusPsi K M C`.
* `NumberField.Chebotarev.frobeniusPsi_sub_sum_frobeniusPsi_le_primePsi`: over the full family,
  the defect is at most `ψ` of the finite set `ramifiedPrimes K L`.
* `NumberField.Chebotarev.frobeniusPsi_sub_sum_frobeniusPsi_isBigO_log`: hence the defect is
  `O(log x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 and Chapter VII, §13.
* R. Sharifi, *Algebraic Number Theory*, the proof of Theorem 7.2.2, where the weighted count over
  an auxiliary compositum is bounded by the weighted count downstairs.
-/

 section

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

open Filter TauCeti
open scoped Asymptotics NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra M L] [IsScalarTower K M L] [IsGalois K L]
  [IsGalois K M]

open scoped Classical in
/-- **The Frobenius weights over a class add up to its own weight.** For a tower `K ⊆ M ⊆ L` with
both `L / K` and `M / K` Galois and a conjugacy class `C` of `Gal(M/K)`, the powered Frobenius
weights at a prime power `𝔭 ^ j` of the classes of `Gal(L/K)` restricting to `C` add up to the
powered Frobenius weight of `C`, provided `𝔭` is unramified in `L`; if `𝔭` ramifies in `L` they add
up to `0`, whatever the weight of `C` is.

At most one summand is ever nonzero, namely the one indexed by the `j`-th power of the Artin class
of `𝔭` in `L / K`; restriction carries it to the `j`-th power of the Artin class of `𝔭` in
`M / K`. -/
theorem solution (C : _root_.ConjClasses (M ≃ₐ[K] M))
    (A : _root_.TauCeti.IdealPrimePower K) :
    ∑ D ∈ {D : _root_.ConjClasses (L ≃ₐ[K] L) |
        ConjClasses.map (_root_.AlgEquiv.restrictNormalHom M) D = C},
        _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight K L D A =
      {B : _root_.TauCeti.IdealPrimePower K | primePowerBase B ∉ _root_.NumberField.Chebotarev.ramifiedPrimes K L}.indicator
        (_root_.NumberField.Chebotarev.frobeniusPrimePowerWeight K M C) A := by
  by_cases hA : _root_.TauCeti.primePowerBase A ∈ _root_.NumberField.Chebotarev.ramifiedPrimes K L
  · -- Every class of `Gal(L/K)` needs an unramifiedness witness in `L`, so all summands vanish.
    rw [_root_.Set.indicator_of_notMem (by simpa using hA)]
    refine _root_.Finset.sum_eq_zero fun D _ ↦ _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_notMem ?_
    intro h
    obtain ⟨hur, -⟩ := mem_frobeniusPrimePowerSet_iff.mp h
    exact (_root_.NumberField.Chebotarev.mem_ramifiedPrimes_iff _).mp hA hur
  · rw [_root_.Set.indicator_of_mem (by simpa using hA)]
    have hurL := not_not.mp ((_root_.NumberField.Chebotarev.mem_ramifiedPrimes_iff _).not.mp hA)
    have hurM := not_not.mp ((_root_.NumberField.Chebotarev.mem_ramifiedPrimes_iff (L := M) _).not.mp
      fun h ↦ hA (_root_.NumberField.Chebotarev.ramifiedPrimes_subset_ramifiedPrimes h))
    -- The unique class of `Gal(L/K)` that can contribute, and its restriction.
    set D₀ := _root_.NumberField.artinSymbol (_root_.TauCeti.primePowerBase A).asIdeal hurL ^ _root_.TauCeti.primePowerExponent A with hD₀def
    have hmap : _root_.ConjClasses.map (_root_.AlgEquiv.restrictNormalHom M) D₀ =
        _root_.NumberField.artinSymbol (_root_.TauCeti.primePowerBase A).asIdeal hurM ^ _root_.TauCeti.primePowerExponent A := by
      rw [hD₀def, _root_.ConjClasses.map_pow, _root_.NumberField.artinSymbol_map_restrictNormalHom]
    -- Membership in the upper fibre of `D` pins `D` down to `D₀`.
    have hmem : ∀ D : _root_.ConjClasses (L ≃ₐ[K] L),
        A ∈ _root_.NumberField.Chebotarev.frobeniusPrimePowerSet K L D ↔ D = D₀ := fun D ↦ by
      rw [_root_.NumberField.Chebotarev.mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hurL D, hD₀def, _root_.eq_comm]
    by_cases hC : _root_.ConjClasses.map (_root_.AlgEquiv.restrictNormalHom M) D₀ = C
    · have hD₀ : D₀ ∈ ({D : _root_.ConjClasses (L ≃ₐ[K] L) |
          ConjClasses.map (_root_.AlgEquiv.restrictNormalHom M) D = C} : _root_.Finset _) :=
        Finset.mem_filter.mpr ⟨_root_.Finset.mem_univ _, hC⟩
      rw [_root_.Finset.sum_eq_single_of_mem D₀ hD₀
        (fun D _ hD ↦ _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_notMem (fun h ↦ hD ((hmem D).mp h))),
        _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_mem ((hmem D₀).mpr _root_.rfl),
        _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_artinSymbol_pow_eq hurM (hmap.symm.trans hC)]
    · rw [_root_.Finset.sum_eq_zero fun D hD ↦ _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_notMem fun h ↦
        hC ((hmem D).mp h ▸ (Finset.mem_filter.mp hD).2)]
      refine (_root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_notMem fun h ↦ hC ?_).symm
      rw [hmap]
      exact (_root_.NumberField.Chebotarev.mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hurM C).mp h







end NumberField.Chebotarev

end
end
